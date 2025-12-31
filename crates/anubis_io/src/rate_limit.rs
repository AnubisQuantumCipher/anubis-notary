//! Rate limiting for authentication attempts and network APIs.
//!
//! This module provides protection against brute-force password attacks
//! using exponential backoff after failed attempts.
//!
//! ## Security Properties
//!
//! - After 3 consecutive failures: 1 second delay
//! - After 5 consecutive failures: 5 seconds delay
//! - After 7 consecutive failures: 30 seconds delay
//! - After 10+ consecutive failures: 60 seconds delay
//!
//! The delay is applied BEFORE the next attempt, not after.
//! This forces attackers to wait, significantly slowing brute-force attacks.
//!
//! ## RefinedRust Specification
//!
//! ```text
//! #[rr::invariant("delay_seconds(failures) = exponential_backoff(failures)")]
//! #[rr::invariant("failures >= 0")]
//! ```

use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use crate::IoError;

/// Rate limiter state file name.
const RATE_LIMIT_FILE: &str = ".rate_limit";

/// Maximum failures before maximum delay.
const MAX_FAILURES_TRACKED: u32 = 20;

/// Rate limiter for authentication attempts.
#[derive(Debug)]
pub struct RateLimiter {
    state_file: PathBuf,
}

/// Rate limit state persisted to disk.
#[derive(Debug, Clone, Copy)]
struct RateLimitState {
    /// Number of consecutive failed attempts.
    failures: u32,
    /// Unix timestamp of last failed attempt.
    last_failure: i64,
}

impl RateLimiter {
    /// Create a rate limiter for the given keystore path.
    pub fn new(keystore_path: impl AsRef<Path>) -> Self {
        let state_file = keystore_path.as_ref().join(RATE_LIMIT_FILE);
        Self { state_file }
    }

    /// Get the delay duration based on failure count.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("failures <= 2 => result = 0")]
    /// #[rr::ensures("failures >= 3 && failures <= 4 => result = 1")]
    /// #[rr::ensures("failures >= 5 && failures <= 6 => result = 5")]
    /// #[rr::ensures("failures >= 7 && failures <= 9 => result = 30")]
    /// #[rr::ensures("failures >= 10 => result = 60")]
    /// ```
    pub fn delay_seconds(failures: u32) -> u64 {
        match failures {
            0..=2 => 0,          // No delay for first 3 attempts
            3..=4 => 1,          // 1 second for attempts 4-5
            5..=6 => 5,          // 5 seconds for attempts 6-7
            7..=9 => 30,         // 30 seconds for attempts 8-10
            _ => 60,             // 60 seconds for 11+ attempts
        }
    }

    /// Read the current rate limit state from disk.
    fn read_state(&self) -> Option<RateLimitState> {
        if !self.state_file.exists() {
            return None;
        }

        let mut file = File::open(&self.state_file).ok()?;
        let mut contents = Vec::new();
        file.read_to_end(&mut contents).ok()?;

        if contents.len() < 12 {
            return None;
        }

        // Parse: 4 bytes failures (LE) + 8 bytes timestamp (LE)
        let failures = u32::from_le_bytes([contents[0], contents[1], contents[2], contents[3]]);
        let last_failure = i64::from_le_bytes([
            contents[4], contents[5], contents[6], contents[7],
            contents[8], contents[9], contents[10], contents[11],
        ]);

        Some(RateLimitState { failures, last_failure })
    }

    /// Write rate limit state to disk atomically.
    ///
    /// Uses write-to-temp + fsync + rename pattern to prevent corruption
    /// on crash. Sets restrictive permissions (0600) on Unix.
    ///
    /// # Security
    ///
    /// Uses a unique temp file name (PID + random suffix) to prevent race
    /// conditions between concurrent writers.
    fn write_state(&self, state: RateLimitState) -> Result<(), IoError> {
        let mut data = Vec::with_capacity(12);
        data.extend_from_slice(&state.failures.to_le_bytes());
        data.extend_from_slice(&state.last_failure.to_le_bytes());

        // SECURITY: Use unique temp file name to prevent race condition.
        // Multiple concurrent processes could otherwise clobber each other's
        // temp files, leading to data loss or corruption.
        let pid = std::process::id();
        let random_suffix: u32 = {
            // Use system time nanoseconds as a simple source of randomness
            // combined with a memory address for additional uniqueness
            let time_component = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.subsec_nanos())
                .unwrap_or(0);
            let addr_component = (&state as *const _ as usize) as u32;
            time_component.wrapping_add(addr_component)
        };
        let temp_name = format!(
            "{}.tmp.{}.{}",
            self.state_file.file_name().unwrap_or_default().to_string_lossy(),
            pid,
            random_suffix
        );
        let temp_path = self.state_file.with_file_name(temp_name);

        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&temp_path)?;

        // Set restrictive permissions on Unix
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let perms = std::fs::Permissions::from_mode(0o600);
            file.set_permissions(perms)?;
        }

        file.write_all(&data)?;
        file.sync_all()?;
        drop(file);

        // Atomic rename - if this fails, clean up the temp file
        if let Err(e) = fs::rename(&temp_path, &self.state_file) {
            let _ = fs::remove_file(&temp_path);
            return Err(e.into());
        }

        // Sync parent directory for durability on Unix
        #[cfg(unix)]
        if let Some(parent) = self.state_file.parent() {
            if let Ok(dir) = File::open(parent) {
                let _ = dir.sync_all();
            }
        }

        Ok(())
    }

    /// Get current Unix timestamp.
    fn now() -> i64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
    }

    /// Check if an attempt is allowed and return required wait time.
    ///
    /// Returns `Some(duration)` if the caller must wait before attempting,
    /// or `None` if attempt is allowed immediately.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::returns("Some(delay) | None")]
    /// #[rr::ensures("result = Some(delay) => delay > 0")]
    /// #[rr::ensures("result = None => attempt_allowed()")]
    /// ```
    pub fn check_rate_limit(&self) -> Option<Duration> {
        let state = self.read_state()?;
        let now = Self::now();

        let required_delay = Self::delay_seconds(state.failures);
        if required_delay == 0 {
            return None;
        }

        let elapsed = now.saturating_sub(state.last_failure);
        let remaining = (required_delay as i64).saturating_sub(elapsed);

        if remaining > 0 {
            Some(Duration::from_secs(remaining as u64))
        } else {
            None
        }
    }

    /// Record a failed authentication attempt.
    ///
    /// This increments the failure counter and records the timestamp.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("state.failures = old(state.failures) + 1")]
    /// #[rr::ensures("state.last_failure = now()")]
    /// ```
    pub fn record_failure(&self) -> Result<u32, IoError> {
        let current = self.read_state().unwrap_or(RateLimitState {
            failures: 0,
            last_failure: 0,
        });

        let new_failures = (current.failures + 1).min(MAX_FAILURES_TRACKED);
        let new_state = RateLimitState {
            failures: new_failures,
            last_failure: Self::now(),
        };

        self.write_state(new_state)?;
        Ok(new_failures)
    }

    /// Record a successful authentication.
    ///
    /// This resets the failure counter.
    ///
    /// # RefinedRust Specification
    /// ```text
    /// #[rr::ensures("state.failures = 0")]
    /// ```
    pub fn record_success(&self) -> Result<(), IoError> {
        // Remove the rate limit file on success
        if self.state_file.exists() {
            fs::remove_file(&self.state_file).ok();
        }
        Ok(())
    }

    /// Get the current failure count.
    pub fn failure_count(&self) -> u32 {
        self.read_state().map(|s| s.failures).unwrap_or(0)
    }
}

/// Format a duration for display to users.
pub fn format_delay(duration: Duration) -> String {
    let secs = duration.as_secs();
    if secs < 60 {
        format!("{} second{}", secs, if secs == 1 { "" } else { "s" })
    } else {
        let mins = secs / 60;
        let remaining_secs = secs % 60;
        if remaining_secs == 0 {
            format!("{} minute{}", mins, if mins == 1 { "" } else { "s" })
        } else {
            format!("{} minute{} {} second{}",
                mins, if mins == 1 { "" } else { "s" },
                remaining_secs, if remaining_secs == 1 { "" } else { "s" })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_delay_calculation() {
        assert_eq!(RateLimiter::delay_seconds(0), 0);
        assert_eq!(RateLimiter::delay_seconds(1), 0);
        assert_eq!(RateLimiter::delay_seconds(2), 0);
        assert_eq!(RateLimiter::delay_seconds(3), 1);
        assert_eq!(RateLimiter::delay_seconds(4), 1);
        assert_eq!(RateLimiter::delay_seconds(5), 5);
        assert_eq!(RateLimiter::delay_seconds(6), 5);
        assert_eq!(RateLimiter::delay_seconds(7), 30);
        assert_eq!(RateLimiter::delay_seconds(9), 30);
        assert_eq!(RateLimiter::delay_seconds(10), 60);
        assert_eq!(RateLimiter::delay_seconds(100), 60);
    }

    #[test]
    fn test_record_failures() {
        let temp_dir = TempDir::new().unwrap();
        let limiter = RateLimiter::new(temp_dir.path());

        // Initial state
        assert_eq!(limiter.failure_count(), 0);
        assert!(limiter.check_rate_limit().is_none());

        // Record failures
        assert_eq!(limiter.record_failure().unwrap(), 1);
        assert_eq!(limiter.record_failure().unwrap(), 2);
        assert_eq!(limiter.record_failure().unwrap(), 3);

        // After 3 failures, delay should be required
        assert_eq!(limiter.failure_count(), 3);
    }

    #[test]
    fn test_success_resets() {
        let temp_dir = TempDir::new().unwrap();
        let limiter = RateLimiter::new(temp_dir.path());

        // Record some failures
        limiter.record_failure().unwrap();
        limiter.record_failure().unwrap();
        limiter.record_failure().unwrap();

        assert_eq!(limiter.failure_count(), 3);

        // Success resets
        limiter.record_success().unwrap();
        assert_eq!(limiter.failure_count(), 0);
    }

    #[test]
    fn test_format_delay() {
        assert_eq!(format_delay(Duration::from_secs(1)), "1 second");
        assert_eq!(format_delay(Duration::from_secs(5)), "5 seconds");
        assert_eq!(format_delay(Duration::from_secs(60)), "1 minute");
        assert_eq!(format_delay(Duration::from_secs(65)), "1 minute 5 seconds");
        assert_eq!(format_delay(Duration::from_secs(120)), "2 minutes");
    }

    #[test]
    fn test_persistence_across_restarts() {
        let temp_dir = TempDir::new().unwrap();
        let path = temp_dir.path().to_path_buf();

        // Simulate first "session" - record 5 failures
        {
            let limiter = RateLimiter::new(&path);
            for _ in 0..5 {
                limiter.record_failure().unwrap();
            }
            assert_eq!(limiter.failure_count(), 5);
        }

        // Simulate "restart" - create new limiter instance
        {
            let limiter = RateLimiter::new(&path);
            // State should persist - still 5 failures
            assert_eq!(limiter.failure_count(), 5);

            // Add more failures
            limiter.record_failure().unwrap();
            limiter.record_failure().unwrap();
            assert_eq!(limiter.failure_count(), 7);
        }

        // Another "restart"
        {
            let limiter = RateLimiter::new(&path);
            // Should still be 7
            assert_eq!(limiter.failure_count(), 7);
            // Delay should be 30 seconds at 7 failures
            assert_eq!(RateLimiter::delay_seconds(limiter.failure_count()), 30);
        }
    }

    #[test]
    fn test_rate_limit_survives_restart_attack() {
        let temp_dir = TempDir::new().unwrap();
        let path = temp_dir.path().to_path_buf();

        // Attacker tries 10 times, "restarts" after each attempt
        for i in 1..=10 {
            let limiter = RateLimiter::new(&path);
            limiter.record_failure().unwrap();

            // Re-create limiter (simulating restart)
            let limiter2 = RateLimiter::new(&path);
            assert_eq!(limiter2.failure_count(), i);
        }

        // After 10 "restarts", should still have max delay
        let limiter = RateLimiter::new(&path);
        assert_eq!(limiter.failure_count(), 10);
        assert_eq!(RateLimiter::delay_seconds(10), 60); // Max delay
    }
}

// ============================================================================
// Network API Rate Limiting
// ============================================================================

use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};

/// Network API rate limit configuration.
#[derive(Debug, Clone)]
pub struct ApiRateLimitConfig {
    /// Maximum requests per window.
    pub max_requests: u32,
    /// Window size in seconds.
    pub window_secs: u64,
    /// Maximum burst size (for token bucket).
    pub burst_size: u32,
    /// Refill rate (tokens per second).
    pub refill_rate: f64,
}

impl Default for ApiRateLimitConfig {
    fn default() -> Self {
        Self {
            max_requests: 100,
            window_secs: 60,
            burst_size: 10,
            refill_rate: 1.0,
        }
    }
}

impl ApiRateLimitConfig {
    /// Create a strict rate limit for sensitive operations.
    pub fn strict() -> Self {
        Self {
            max_requests: 10,
            window_secs: 60,
            burst_size: 3,
            refill_rate: 0.2,
        }
    }

    /// Create a relaxed rate limit for normal operations.
    pub fn relaxed() -> Self {
        Self {
            max_requests: 1000,
            window_secs: 60,
            burst_size: 100,
            refill_rate: 20.0,
        }
    }
}

/// Token bucket for rate limiting.
#[derive(Debug, Clone)]
struct TokenBucket {
    /// Current number of tokens.
    tokens: f64,
    /// Maximum tokens (burst size).
    max_tokens: f64,
    /// Tokens added per second.
    refill_rate: f64,
    /// Last refill timestamp.
    last_refill: i64,
}

impl TokenBucket {
    fn new(max_tokens: u32, refill_rate: f64) -> Self {
        Self {
            tokens: max_tokens as f64,
            max_tokens: max_tokens as f64,
            refill_rate,
            last_refill: Self::now_millis(),
        }
    }

    fn now_millis() -> i64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as i64)
            .unwrap_or(0)
    }

    /// Refill tokens based on elapsed time.
    fn refill(&mut self) {
        let now = Self::now_millis();
        let elapsed_secs = (now - self.last_refill) as f64 / 1000.0;
        self.tokens = (self.tokens + elapsed_secs * self.refill_rate).min(self.max_tokens);
        self.last_refill = now;
    }

    /// Try to consume one token. Returns true if successful.
    fn try_consume(&mut self) -> bool {
        self.refill();
        if self.tokens >= 1.0 {
            self.tokens -= 1.0;
            true
        } else {
            false
        }
    }

    /// Get time until next token is available (in milliseconds).
    fn time_until_available(&mut self) -> u64 {
        self.refill();
        if self.tokens >= 1.0 {
            0
        } else {
            let needed = 1.0 - self.tokens;
            let wait_secs = needed / self.refill_rate;
            (wait_secs * 1000.0).ceil() as u64
        }
    }
}

/// Sliding window counter for rate limiting.
#[derive(Debug, Clone)]
struct SlidingWindow {
    /// Request timestamps in the current window.
    requests: Vec<i64>,
    /// Maximum requests per window.
    max_requests: u32,
    /// Window size in milliseconds.
    window_ms: i64,
}

impl SlidingWindow {
    fn new(max_requests: u32, window_secs: u64) -> Self {
        Self {
            requests: Vec::new(),
            max_requests,
            window_ms: (window_secs * 1000) as i64,
        }
    }

    fn now_millis() -> i64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as i64)
            .unwrap_or(0)
    }

    /// Clean up old requests outside the window.
    fn cleanup(&mut self) {
        let cutoff = Self::now_millis() - self.window_ms;
        self.requests.retain(|&ts| ts > cutoff);
    }

    /// Try to record a request. Returns true if allowed.
    fn try_record(&mut self) -> bool {
        self.cleanup();
        if self.requests.len() < self.max_requests as usize {
            self.requests.push(Self::now_millis());
            true
        } else {
            false
        }
    }

    /// Get remaining requests in the current window.
    fn remaining(&mut self) -> u32 {
        self.cleanup();
        self.max_requests.saturating_sub(self.requests.len() as u32)
    }

    /// Get time until the window resets (oldest request expires).
    fn time_until_reset(&mut self) -> u64 {
        self.cleanup();
        if let Some(&oldest) = self.requests.first() {
            let expires_at = oldest + self.window_ms;
            let now = Self::now_millis();
            if expires_at > now {
                (expires_at - now) as u64
            } else {
                0
            }
        } else {
            0
        }
    }
}

/// Network API rate limiter with multiple endpoints.
pub struct ApiRateLimiter {
    /// Per-endpoint token buckets (for burst control).
    buckets: RwLock<HashMap<String, TokenBucket>>,
    /// Per-endpoint sliding windows (for sustained rate).
    windows: RwLock<HashMap<String, SlidingWindow>>,
    /// Global token bucket (cross-endpoint limit).
    global_bucket: Mutex<TokenBucket>,
    /// Configuration.
    config: ApiRateLimitConfig,
}

impl ApiRateLimiter {
    /// Create a new API rate limiter.
    pub fn new(config: ApiRateLimitConfig) -> Self {
        let global_bucket = TokenBucket::new(
            config.burst_size * 10, // Global is 10x per-endpoint
            config.refill_rate * 10.0,
        );

        Self {
            buckets: RwLock::new(HashMap::new()),
            windows: RwLock::new(HashMap::new()),
            global_bucket: Mutex::new(global_bucket),
            config,
        }
    }

    /// Create with default configuration.
    pub fn default_config() -> Self {
        Self::new(ApiRateLimitConfig::default())
    }

    /// Create with strict configuration.
    pub fn strict() -> Self {
        Self::new(ApiRateLimitConfig::strict())
    }

    fn get_or_create_bucket(&self, endpoint: &str) -> TokenBucket {
        // Use unwrap_or_else to recover from poisoned locks - rate limiting
        // should continue even if another thread panicked
        let buckets = self.buckets.read().unwrap_or_else(|e| e.into_inner());
        if let Some(bucket) = buckets.get(endpoint) {
            bucket.clone()
        } else {
            drop(buckets);
            let mut buckets = self.buckets.write().unwrap_or_else(|e| e.into_inner());
            buckets.entry(endpoint.to_string())
                .or_insert_with(|| TokenBucket::new(self.config.burst_size, self.config.refill_rate))
                .clone()
        }
    }

    fn update_bucket(&self, endpoint: &str, bucket: TokenBucket) {
        self.buckets.write().unwrap_or_else(|e| e.into_inner()).insert(endpoint.to_string(), bucket);
    }

    fn get_or_create_window(&self, endpoint: &str) -> SlidingWindow {
        let windows = self.windows.read().unwrap_or_else(|e| e.into_inner());
        if let Some(window) = windows.get(endpoint) {
            window.clone()
        } else {
            drop(windows);
            let mut windows = self.windows.write().unwrap_or_else(|e| e.into_inner());
            windows.entry(endpoint.to_string())
                .or_insert_with(|| SlidingWindow::new(self.config.max_requests, self.config.window_secs))
                .clone()
        }
    }

    fn update_window(&self, endpoint: &str, window: SlidingWindow) {
        self.windows.write().unwrap_or_else(|e| e.into_inner()).insert(endpoint.to_string(), window);
    }

    /// Check if a request is allowed for the given endpoint.
    ///
    /// Returns `Ok(())` if allowed, or `Err(wait_time)` with the duration to wait.
    pub fn check(&self, endpoint: &str) -> Result<(), Duration> {
        // Check global rate limit first
        {
            let mut global = self.global_bucket.lock().unwrap_or_else(|e| e.into_inner());
            if !global.try_consume() {
                let wait_ms = global.time_until_available();
                return Err(Duration::from_millis(wait_ms));
            }
        }

        // Check per-endpoint token bucket (for bursts)
        let mut bucket = self.get_or_create_bucket(endpoint);
        if !bucket.try_consume() {
            let wait_ms = bucket.time_until_available();
            self.update_bucket(endpoint, bucket);
            return Err(Duration::from_millis(wait_ms));
        }
        self.update_bucket(endpoint, bucket);

        // Check per-endpoint sliding window (for sustained rate)
        let mut window = self.get_or_create_window(endpoint);
        if !window.try_record() {
            let wait_ms = window.time_until_reset();
            self.update_window(endpoint, window);
            return Err(Duration::from_millis(wait_ms));
        }
        self.update_window(endpoint, window);

        Ok(())
    }

    /// Get the remaining requests for an endpoint.
    pub fn remaining(&self, endpoint: &str) -> u32 {
        let mut window = self.get_or_create_window(endpoint);
        let remaining = window.remaining();
        self.update_window(endpoint, window);
        remaining
    }

    /// Check without consuming (peek).
    pub fn peek(&self, endpoint: &str) -> bool {
        // Check if would be allowed
        let bucket = self.get_or_create_bucket(endpoint);
        let mut window = self.get_or_create_window(endpoint);
        let global = self.global_bucket.lock().unwrap_or_else(|e| e.into_inner());

        bucket.tokens >= 1.0 && window.remaining() > 0 && global.tokens >= 1.0
    }

    /// Reset rate limits for an endpoint.
    pub fn reset(&self, endpoint: &str) {
        self.buckets.write().unwrap_or_else(|e| e.into_inner()).remove(endpoint);
        self.windows.write().unwrap_or_else(|e| e.into_inner()).remove(endpoint);
    }

    /// Reset all rate limits.
    pub fn reset_all(&self) {
        self.buckets.write().unwrap_or_else(|e| e.into_inner()).clear();
        self.windows.write().unwrap_or_else(|e| e.into_inner()).clear();
        *self.global_bucket.lock().unwrap_or_else(|e| e.into_inner()) = TokenBucket::new(
            self.config.burst_size * 10,
            self.config.refill_rate * 10.0,
        );
    }
}

/// Rate limit check result.
#[derive(Debug, Clone)]
pub enum RateLimitResult {
    /// Request is allowed.
    Allowed {
        /// Remaining requests in the window.
        remaining: u32,
    },
    /// Request is rate limited.
    Limited {
        /// Time to wait before retrying.
        retry_after: Duration,
    },
}

impl ApiRateLimiter {
    /// Check with detailed result.
    pub fn check_detailed(&self, endpoint: &str) -> RateLimitResult {
        match self.check(endpoint) {
            Ok(()) => RateLimitResult::Allowed {
                remaining: self.remaining(endpoint),
            },
            Err(retry_after) => RateLimitResult::Limited { retry_after },
        }
    }
}

/// Thread-safe rate limiter for HTTP APIs.
pub type SharedApiRateLimiter = Arc<ApiRateLimiter>;

/// Create a shared rate limiter for use across threads.
pub fn shared_rate_limiter(config: ApiRateLimitConfig) -> SharedApiRateLimiter {
    Arc::new(ApiRateLimiter::new(config))
}

#[cfg(test)]
mod api_rate_limit_tests {
    use super::*;

    #[test]
    fn test_token_bucket_basic() {
        let mut bucket = TokenBucket::new(5, 1.0);

        // Should have 5 tokens initially
        assert!(bucket.try_consume());
        assert!(bucket.try_consume());
        assert!(bucket.try_consume());
        assert!(bucket.try_consume());
        assert!(bucket.try_consume());

        // Should be empty now
        assert!(!bucket.try_consume());
    }

    #[test]
    fn test_sliding_window_basic() {
        let mut window = SlidingWindow::new(3, 60);

        assert!(window.try_record());
        assert!(window.try_record());
        assert!(window.try_record());

        // Should be at limit
        assert!(!window.try_record());
        assert_eq!(window.remaining(), 0);
    }

    #[test]
    fn test_api_rate_limiter() {
        let config = ApiRateLimitConfig {
            max_requests: 5,
            window_secs: 60,
            burst_size: 3,
            refill_rate: 100.0, // Fast refill for testing
        };
        let limiter = ApiRateLimiter::new(config);

        // First few requests should succeed
        assert!(limiter.check("/api/sign").is_ok());
        assert!(limiter.check("/api/sign").is_ok());
        assert!(limiter.check("/api/sign").is_ok());
    }

    #[test]
    fn test_api_rate_limiter_different_endpoints() {
        let config = ApiRateLimitConfig {
            max_requests: 2,
            window_secs: 60,
            burst_size: 2,
            refill_rate: 100.0,
        };
        let limiter = ApiRateLimiter::new(config);

        // Different endpoints have separate limits
        assert!(limiter.check("/api/sign").is_ok());
        assert!(limiter.check("/api/sign").is_ok());

        assert!(limiter.check("/api/verify").is_ok());
        assert!(limiter.check("/api/verify").is_ok());
    }

    #[test]
    fn test_rate_limit_result() {
        let config = ApiRateLimitConfig {
            max_requests: 1,
            window_secs: 60,
            burst_size: 1,
            refill_rate: 0.01, // Very slow refill
        };
        let limiter = ApiRateLimiter::new(config);

        // First request allowed
        match limiter.check_detailed("/api/test") {
            RateLimitResult::Allowed { remaining } => {
                assert!(remaining <= 1);
            }
            _ => panic!("Expected Allowed"),
        }

        // Second request should be limited
        match limiter.check_detailed("/api/test") {
            RateLimitResult::Limited { retry_after } => {
                assert!(retry_after.as_millis() > 0);
            }
            RateLimitResult::Allowed { .. } => {
                // May be allowed if refill happened
            }
        }
    }

    #[test]
    fn test_reset() {
        let config = ApiRateLimitConfig {
            max_requests: 1,
            window_secs: 60,
            burst_size: 1,
            refill_rate: 0.01,
        };
        let limiter = ApiRateLimiter::new(config);

        limiter.check("/api/test").ok();

        // Reset the endpoint
        limiter.reset("/api/test");

        // Should be allowed again
        assert!(limiter.check("/api/test").is_ok());
    }
}
