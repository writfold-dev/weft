//! Bounded JSON parsing for peer protocol frames.
//!
//! Peer frames are untrusted bytes. This parser validates the complete JSON
//! grammar, rejects duplicate object keys, preserves number lexical tokens and
//! enforces the container/value bounds of the consumed transport contract. It
//! never repairs, defaults or replaces malformed input.

/// Bounds mirrored from the consumed writfold.agent/1 transport contract.
#[derive(Clone, Copy)]
pub struct Bounds {
    pub depth: usize,
    pub nodes: usize,
    pub entries: usize,
}
impl Bounds {
    pub const fn transport() -> Self {
        Self {
            depth: 1024,
            nodes: 65536,
            entries: 65536,
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Number(Box<str>),
    Text(Box<str>),
    Array(Vec<Value>),
    Object(Vec<(Box<str>, Value)>),
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseError {
    Depth,
    Nodes,
    Entries,
    Empty,
    Trailing,
    DuplicateKey,
    Literal,
    Number,
    String,
    Escape,
    Surrogate,
    Control,
    Utf8,
}
struct Parser<'s> {
    source: &'s [u8],
    at: usize,
    bounds: Bounds,
    depth: usize,
    nodes: usize,
}
/// Parses exactly one JSON value; trailing non-whitespace bytes are an error.
pub fn parse(frame: &[u8], bounds: Bounds) -> Result<Value, ParseError> {
    let mut parser = Parser {
        source: frame,
        at: 0,
        bounds,
        depth: 0,
        nodes: 0,
    };
    let value = parser.value()?;
    parser.whitespace();
    if parser.at != frame.len() {
        return Err(ParseError::Trailing);
    }
    Ok(value)
}
impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.source.get(self.at).copied()
    }
    fn eat(&mut self, byte: u8) -> bool {
        if self.peek() == Some(byte) {
            self.at += 1;
            true
        } else {
            false
        }
    }
    fn whitespace(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.at += 1;
        }
    }
    fn counted(&mut self) -> Result<(), ParseError> {
        self.nodes = self.nodes.checked_add(1).ok_or(ParseError::Nodes)?;
        if self.nodes > self.bounds.nodes {
            return Err(ParseError::Nodes);
        }
        Ok(())
    }
    fn value(&mut self) -> Result<Value, ParseError> {
        self.whitespace();
        self.counted()?;
        match self.peek().ok_or(ParseError::Empty)? {
            b'n' => self.literal(b"null", Value::Null),
            b't' => self.literal(b"true", Value::Bool(true)),
            b'f' => self.literal(b"false", Value::Bool(false)),
            b'"' => {
                self.at += 1;
                Ok(Value::Text(self.string()?))
            }
            b'[' => self.array(),
            b'{' => self.object(),
            b'-' | b'0'..=b'9' => self.number(),
            _ => Err(ParseError::Literal),
        }
    }
    fn literal(&mut self, word: &[u8], value: Value) -> Result<Value, ParseError> {
        if self.source.len() - self.at < word.len()
            || &self.source[self.at..self.at + word.len()] != word
        {
            return Err(ParseError::Literal);
        }
        self.at += word.len();
        Ok(value)
    }
    fn number(&mut self) -> Result<Value, ParseError> {
        let start = self.at;
        self.eat(b'-');
        match self.peek() {
            Some(b'0') => self.at += 1,
            Some(b'1'..=b'9') => {
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.at += 1;
                }
            }
            _ => return Err(ParseError::Number),
        }
        if self.eat(b'.') {
            let digits_start = self.at;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.at += 1;
            }
            if self.at == digits_start {
                return Err(ParseError::Number);
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.at += 1;
            self.eat(b'+' | b'-');
            let digits_start = self.at;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.at += 1;
            }
            if self.at == digits_start {
                return Err(ParseError::Number);
            }
        }
        let token = &self.source[start..self.at];
        let text = std::str::from_utf8(token).map_err(|_| ParseError::Utf8)?;
        Ok(Value::Number(text.into()))
    }
    fn container(&mut self) -> Result<(), ParseError> {
        self.depth = self.depth.checked_add(1).ok_or(ParseError::Depth)?;
        if self.depth > self.bounds.depth {
            return Err(ParseError::Depth);
        }
        Ok(())
    }
    fn array(&mut self) -> Result<Value, ParseError> {
        self.container()?;
        self.at += 1;
        let mut items = Vec::new();
        self.whitespace();
        if self.eat(b']') {
            self.depth -= 1;
            return Ok(Value::Array(items));
        }
        loop {
            if items.len() >= self.bounds.entries {
                return Err(ParseError::Entries);
            }
            items.push(self.value()?);
            self.whitespace();
            if self.eat(b',') {
                continue;
            }
            if self.eat(b']') {
                self.depth -= 1;
                return Ok(Value::Array(items));
            }
            return Err(ParseError::Literal);
        }
    }
    fn object(&mut self) -> Result<Value, ParseError> {
        self.container()?;
        self.at += 1;
        let mut members = Vec::new();
        self.whitespace();
        if self.eat(b'}') {
            self.depth -= 1;
            return Ok(Value::Object(members));
        }
        loop {
            if members.len() >= self.bounds.entries {
                return Err(ParseError::Entries);
            }
            if !self.eat(b'"') {
                return Err(ParseError::Literal);
            }
            let key = self.string()?;
            self.whitespace();
            if !self.eat(b':') {
                return Err(ParseError::Literal);
            }
            let value = self.value()?;
            if members
                .iter()
                .any(|(known, _): &(Box<str>, Value)| known == &key)
            {
                return Err(ParseError::DuplicateKey);
            }
            members.push((key, value));
            self.whitespace();
            if self.eat(b',') {
                self.whitespace();
                continue;
            }
            if self.eat(b'}') {
                self.depth -= 1;
                return Ok(Value::Object(members));
            }
            return Err(ParseError::Literal);
        }
    }
    fn string(&mut self) -> Result<Box<str>, ParseError> {
        let mut decoded = String::new();
        loop {
            let byte = self.peek().ok_or(ParseError::String)?;
            match byte {
                b'"' => {
                    self.at += 1;
                    return Ok(decoded.into_boxed_str());
                }
                b'\\' => {
                    self.at += 1;
                    self.escape(&mut decoded)?;
                }
                0x00..=0x1f => return Err(ParseError::Control),
                _ => {
                    let start = self.at;
                    while !matches!(self.peek(), None | Some(b'"' | b'\\') | Some(0x00..=0x1f)) {
                        self.at += 1;
                    }
                    decoded.push_str(
                        std::str::from_utf8(&self.source[start..self.at])
                            .map_err(|_| ParseError::Utf8)?,
                    );
                }
            }
        }
    }
    fn escape(&mut self, decoded: &mut String) -> Result<(), ParseError> {
        let simple = match self.peek().ok_or(ParseError::Escape)? {
            b'"' => '"',
            b'\\' => '\\',
            b'/' => '/',
            b'b' => '\u{8}',
            b'f' => '\u{c}',
            b'n' => '\n',
            b'r' => '\r',
            b't' => '\t',
            b'u' => {
                let first = self.hex4()?;
                let character = match first {
                    0xd800..=0xdbff => {
                        if !self.eat(b'\\') || !self.eat(b'u') {
                            return Err(ParseError::Surrogate);
                        }
                        let second = self.hex4()?;
                        if !matches!(second, 0xdc00..=0xdfff) {
                            return Err(ParseError::Surrogate);
                        }
                        let combined = 0x10000 + ((first - 0xd800) << 10) + (second - 0xdc00);
                        char::from_u32(combined).ok_or(ParseError::Surrogate)?
                    }
                    0xdc00..=0xdfff => return Err(ParseError::Surrogate),
                    value => char::from_u32(value).ok_or(ParseError::Escape)?,
                };
                decoded.push(character);
                return Ok(());
            }
            _ => return Err(ParseError::Escape),
        };
        decoded.push(simple);
        self.at += 1;
        Ok(())
    }
    fn hex4(&mut self) -> Result<u32, ParseError> {
        self.at += 1;
        if self.at + 4 > self.source.len() {
            return Err(ParseError::Escape);
        }
        let token = std::str::from_utf8(&self.source[self.at..self.at + 4])
            .map_err(|_| ParseError::Escape)?;
        let value = u32::from_str_radix(token, 16).map_err(|_| ParseError::Escape)?;
        if !token.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(ParseError::Escape);
        }
        self.at += 4;
        Ok(value)
    }
}
