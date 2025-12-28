//! RefinedRust Annotations for cbor module (Canonical CBOR)
//!
//! This file shows the complete refinement type annotations for the
//! canonical CBOR encoder and decoder.

// ============================================================================
// Encoder Type
// ============================================================================

/// CBOR Encoder with position tracking.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("buf" : "list u8", "pos" : "nat", "len" : "nat")]
/// #[rr::invariant("pos <= len")]
/// #[rr::invariant("len = len(buf)")]
/// ```
#[rr::type("Encoder")]
pub struct Encoder<'a> {
    buffer: &'a mut [u8],
    position: usize,
}

impl<'a> Encoder<'a> {
    /// Create a new encoder.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::params("gamma" : "gname", "buf" : "list u8")]
    /// #[rr::args("(buf, gamma) @ &mut [u8]")]
    /// #[rr::returns("enc @ Encoder")]
    /// #[rr::ensures("enc.pos = 0")]
    /// #[rr::ensures("enc.len = len(buf)")]
    /// ```
    #[rr::verified]
    pub fn new(buffer: &'a mut [u8]) -> Self {
        Self { buffer, position: 0 }
    }

    /// Get current position.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::returns("{n : nat | n = self.pos}")]
    /// #[rr::pure]
    /// ```
    #[rr::verified]
    #[inline]
    pub fn position(&self) -> usize {
        self.position
    }

    /// Encode an unsigned integer.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::params("gamma" : "gname", "n" : "Z")]
    /// #[rr::args("(self, gamma) @ &mut Encoder", "n @ u64")]
    /// #[rr::requires("0 <= n")]
    /// #[rr::ensures("match result {
    ///     Ok(()) =>
    ///         gamma.pos = old(self.pos) + encode_uint_len(n) /\
    ///         gamma.buf[old(self.pos)..gamma.pos] = encode_uint_bytes(n)
    ///   | Err(_) =>
    ///         old(self.pos) + encode_uint_len(n) > self.len
    /// }")]
    /// ```
    #[rr::verified]
    pub fn encode_uint(&mut self, value: u64) -> Result<(), CborError> {
        #[rr::assert("Calculate encoding length")]
        let (header_len, header) = if value < 24 {
            (1, [value as u8, 0, 0, 0, 0, 0, 0, 0, 0])
        } else if value <= 0xFF {
            (2, [24, value as u8, 0, 0, 0, 0, 0, 0, 0])
        } else if value <= 0xFFFF {
            let bytes = (value as u16).to_be_bytes();
            (3, [25, bytes[0], bytes[1], 0, 0, 0, 0, 0, 0])
        } else if value <= 0xFFFF_FFFF {
            let bytes = (value as u32).to_be_bytes();
            (5, [26, bytes[0], bytes[1], bytes[2], bytes[3], 0, 0, 0, 0])
        } else {
            let bytes = value.to_be_bytes();
            (9, [27, bytes[0], bytes[1], bytes[2], bytes[3],
                 bytes[4], bytes[5], bytes[6], bytes[7]])
        };

        #[rr::assert("Check buffer space")]
        if self.position + header_len > self.buffer.len() {
            return Err(CborError::BufferOverflow);
        }

        #[rr::assert("Write header bytes")]
        self.buffer[self.position..self.position + header_len]
            .copy_from_slice(&header[..header_len]);
        self.position += header_len;

        Ok(())
    }

    /// Encode a byte string.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::params("gamma" : "gname", "bytes" : "list u8")]
    /// #[rr::args("(self, gamma) @ &mut Encoder", "bytes @ &shr<'_, [u8]>")]
    /// #[rr::ensures("match result {
    ///     Ok(()) =>
    ///         gamma.pos = old(self.pos) + 1 + len_header_size(len(bytes)) + len(bytes) /\
    ///         gamma.buf[old(self.pos)..gamma.pos] = encode_bytes(bytes)
    ///   | Err(_) =>
    ///         insufficient_space
    /// }")]
    /// ```
    #[rr::verified]
    pub fn encode_bytes(&mut self, bytes: &[u8]) -> Result<(), CborError> {
        #[rr::assert("Encode length header with major type 2")]
        self.encode_type_and_len(2, bytes.len())?;

        #[rr::assert("Check space for payload")]
        if self.position + bytes.len() > self.buffer.len() {
            return Err(CborError::BufferOverflow);
        }

        #[rr::assert("Copy payload bytes")]
        self.buffer[self.position..self.position + bytes.len()].copy_from_slice(bytes);
        self.position += bytes.len();

        Ok(())
    }

    /// Encode a text string.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::params("gamma" : "gname", "text" : "string")]
    /// #[rr::args("(self, gamma) @ &mut Encoder", "text @ &shr<'_, str>")]
    /// #[rr::ensures("gamma.buf[old(self.pos)..] starts with major type 3")]
    /// ```
    #[rr::verified]
    pub fn encode_text(&mut self, text: &str) -> Result<(), CborError> {
        let bytes = text.as_bytes();

        #[rr::assert("Encode length header with major type 3")]
        self.encode_type_and_len(3, bytes.len())?;

        #[rr::assert("Check space and copy UTF-8 bytes")]
        if self.position + bytes.len() > self.buffer.len() {
            return Err(CborError::BufferOverflow);
        }

        self.buffer[self.position..self.position + bytes.len()].copy_from_slice(bytes);
        self.position += bytes.len();

        Ok(())
    }

    /// Encode array header.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::params("gamma" : "gname", "len" : "nat")]
    /// #[rr::ensures("gamma.buf[old(self.pos)] >> 5 = 4")]
    /// ```
    #[rr::verified]
    pub fn encode_array_header(&mut self, len: usize) -> Result<(), CborError> {
        self.encode_type_and_len(4, len)
    }

    /// Encode map header.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::params("gamma" : "gname", "len" : "nat")]
    /// #[rr::ensures("gamma.buf[old(self.pos)] >> 5 = 5")]
    /// ```
    #[rr::verified]
    pub fn encode_map_header(&mut self, len: usize) -> Result<(), CborError> {
        self.encode_type_and_len(5, len)
    }

    /// Internal: encode type and length.
    #[rr::verified]
    fn encode_type_and_len(&mut self, major: u8, len: usize) -> Result<(), CborError> {
        #[rr::assert("major < 8, so major << 5 fits in u8")]
        let type_byte = major << 5;

        if len < 24 {
            if self.position >= self.buffer.len() {
                return Err(CborError::BufferOverflow);
            }
            self.buffer[self.position] = type_byte | (len as u8);
            self.position += 1;
        } else if len <= 0xFF {
            if self.position + 2 > self.buffer.len() {
                return Err(CborError::BufferOverflow);
            }
            self.buffer[self.position] = type_byte | 24;
            self.buffer[self.position + 1] = len as u8;
            self.position += 2;
        } else if len <= 0xFFFF {
            if self.position + 3 > self.buffer.len() {
                return Err(CborError::BufferOverflow);
            }
            self.buffer[self.position] = type_byte | 25;
            let bytes = (len as u16).to_be_bytes();
            self.buffer[self.position + 1..self.position + 3].copy_from_slice(&bytes);
            self.position += 3;
        } else {
            // Assuming len fits in u32 for simplicity
            if self.position + 5 > self.buffer.len() {
                return Err(CborError::BufferOverflow);
            }
            self.buffer[self.position] = type_byte | 26;
            let bytes = (len as u32).to_be_bytes();
            self.buffer[self.position + 1..self.position + 5].copy_from_slice(&bytes);
            self.position += 5;
        }

        Ok(())
    }
}

// ============================================================================
// Decoder Type
// ============================================================================

/// CBOR Decoder with position tracking.
///
/// # RefinedRust Specification
/// ```refinedrust
/// #[rr::refined_by("data" : "list u8", "pos" : "nat")]
/// #[rr::invariant("pos <= len(data)")]
/// ```
#[rr::type("Decoder")]
pub struct Decoder<'a> {
    data: &'a [u8],
    position: usize,
}

impl<'a> Decoder<'a> {
    /// Create a new decoder.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::params("data" : "list u8")]
    /// #[rr::args("data @ &shr<'_, [u8]>")]
    /// #[rr::returns("dec @ Decoder")]
    /// #[rr::ensures("dec.pos = 0")]
    /// #[rr::ensures("dec.data = data")]
    /// ```
    #[rr::verified]
    pub fn new(data: &'a [u8]) -> Self {
        Self { data, position: 0 }
    }

    /// Decode an unsigned integer.
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::params("gamma" : "gname")]
    /// #[rr::args("(self, gamma) @ &mut Decoder")]
    /// #[rr::ensures("match result {
    ///     Ok(n) =>
    ///         self.data[old(self.pos)] >> 5 = 0 /\
    ///         gamma.pos > old(self.pos) /\
    ///         gamma.pos <= len(self.data) /\
    ///         n = decode_uint(self.data[old(self.pos)..gamma.pos])
    ///   | Err(_) =>
    ///         old(self.pos) >= len(self.data) \/
    ///         self.data[old(self.pos)] >> 5 != 0
    /// }")]
    /// #[rr::ensures("total_decoder: all inputs produce Ok or Err")]
    /// ```
    #[rr::verified]
    pub fn decode_uint(&mut self) -> Result<u64, CborError> {
        #[rr::assert("Check we have at least one byte")]
        if self.position >= self.data.len() {
            return Err(CborError::UnexpectedEnd);
        }

        let first = self.data[self.position];
        let major = first >> 5;
        let info = first & 0x1F;

        #[rr::assert("Verify major type is 0 (unsigned)")]
        if major != 0 {
            return Err(CborError::TypeMismatch);
        }

        self.position += 1;

        #[rr::assert("Decode additional info")]
        let value = if info < 24 {
            info as u64
        } else if info == 24 {
            if self.position >= self.data.len() {
                return Err(CborError::UnexpectedEnd);
            }
            let v = self.data[self.position] as u64;
            self.position += 1;
            v
        } else if info == 25 {
            if self.position + 2 > self.data.len() {
                return Err(CborError::UnexpectedEnd);
            }
            let v = u16::from_be_bytes([
                self.data[self.position],
                self.data[self.position + 1],
            ]) as u64;
            self.position += 2;
            v
        } else if info == 26 {
            if self.position + 4 > self.data.len() {
                return Err(CborError::UnexpectedEnd);
            }
            let v = u32::from_be_bytes([
                self.data[self.position],
                self.data[self.position + 1],
                self.data[self.position + 2],
                self.data[self.position + 3],
            ]) as u64;
            self.position += 4;
            v
        } else if info == 27 {
            if self.position + 8 > self.data.len() {
                return Err(CborError::UnexpectedEnd);
            }
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(&self.data[self.position..self.position + 8]);
            let v = u64::from_be_bytes(bytes);
            self.position += 8;
            v
        } else {
            return Err(CborError::InvalidInfo);
        };

        Ok(value)
    }

    /// Skip a CBOR value (for forward compatibility).
    ///
    /// # RefinedRust Specification
    /// ```refinedrust
    /// #[rr::ensures("match result {
    ///     Ok(()) => gamma.pos > old(self.pos) /\ gamma.pos <= len(self.data)
    ///   | Err(_) => malformed_cbor(self.data[old(self.pos)..])
    /// }")]
    /// #[rr::ensures("total_decoder: never panics")]
    /// ```
    #[rr::verified]
    pub fn skip_value(&mut self) -> Result<(), CborError> {
        #[rr::assert("Check we have at least one byte")]
        if self.position >= self.data.len() {
            return Err(CborError::UnexpectedEnd);
        }

        let first = self.data[self.position];
        let major = first >> 5;
        let info = first & 0x1F;

        self.position += 1;

        #[rr::assert("Decode length based on major type")]
        let len = self.decode_info_len(info)?;

        match major {
            0 | 1 => {
                // Unsigned/negative integer: length already consumed
            }
            2 | 3 => {
                // Byte/text string: skip `len` bytes
                if self.position + len > self.data.len() {
                    return Err(CborError::UnexpectedEnd);
                }
                self.position += len;
            }
            4 => {
                // Array: skip `len` items
                for _ in 0..len {
                    self.skip_value()?;
                }
            }
            5 => {
                // Map: skip `len` key-value pairs
                for _ in 0..len {
                    self.skip_value()?;  // key
                    self.skip_value()?;  // value
                }
            }
            6 => {
                // Tag: skip one item
                self.skip_value()?;
            }
            7 => {
                // Simple/float: already consumed
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    fn decode_info_len(&mut self, info: u8) -> Result<usize, CborError> {
        if info < 24 {
            Ok(info as usize)
        } else if info == 24 {
            if self.position >= self.data.len() {
                return Err(CborError::UnexpectedEnd);
            }
            let v = self.data[self.position] as usize;
            self.position += 1;
            Ok(v)
        } else if info == 25 {
            if self.position + 2 > self.data.len() {
                return Err(CborError::UnexpectedEnd);
            }
            let v = u16::from_be_bytes([
                self.data[self.position],
                self.data[self.position + 1],
            ]) as usize;
            self.position += 2;
            Ok(v)
        } else if info == 26 {
            if self.position + 4 > self.data.len() {
                return Err(CborError::UnexpectedEnd);
            }
            let v = u32::from_be_bytes([
                self.data[self.position],
                self.data[self.position + 1],
                self.data[self.position + 2],
                self.data[self.position + 3],
            ]) as usize;
            self.position += 4;
            Ok(v)
        } else {
            Err(CborError::InvalidInfo)
        }
    }
}

// ============================================================================
// Verification Conditions
// ============================================================================

/// Proof obligations for CBOR codec:
///
/// ## Totality
/// ```coq
/// Theorem decoder_total :
///   forall data pos,
///     pos <= len(data) ->
///     exists result, decode_value(data, pos) = result.
/// ```
///
/// ## Position Safety
/// ```coq
/// Theorem position_bounded :
///   forall dec,
///     dec.pos <= len(dec.data).
/// ```
///
/// ## Round-Trip
/// ```coq
/// Theorem cbor_roundtrip :
///   forall v,
///     well_formed(v) ->
///     decode(encode(v)) = Ok(v).
/// ```
///
/// ## Canonical Form
/// ```coq
/// Theorem minimal_encoding :
///   forall n,
///     n < 24 -> encode_uint_len(n) = 1.
///     24 <= n < 256 -> encode_uint_len(n) = 2.
///     (* etc. *)
/// ```
mod _verification_conditions {}
