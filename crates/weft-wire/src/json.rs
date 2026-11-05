use std::fmt::{self, Write};

#[derive(Debug, PartialEq, Eq)]
pub enum RenderError {
    OutputLimit,
    InvalidRecord(&'static str),
}
pub type Result<T, E = RenderError> = std::result::Result<T, E>;

impl fmt::Display for RenderError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutputLimit => formatter.write_str("complete report exceeds output byte limit"),
            Self::InvalidRecord(reason) => write!(formatter, "invalid report record: {reason}"),
        }
    }
}
impl std::error::Error for RenderError {}

pub(crate) struct Json {
    bytes: Vec<u8>,
    limit: usize,
    pretty: bool,
    depth: usize,
    first: Vec<bool>,
}
impl Json {
    pub(crate) fn new(limit: usize, pretty: bool) -> Self {
        Self {
            bytes: Vec::new(),
            limit,
            pretty,
            depth: 0,
            first: Vec::new(),
        }
    }
    pub(crate) fn finish(self) -> Vec<u8> {
        self.bytes
    }
    pub(crate) fn raw(&mut self, text: &str) -> Result<()> {
        let remaining = self
            .limit
            .checked_sub(self.bytes.len())
            .ok_or(RenderError::OutputLimit)?;
        if text.len() > remaining {
            return Err(RenderError::OutputLimit);
        }
        self.bytes.extend_from_slice(text.as_bytes());
        Ok(())
    }
    pub(crate) fn string(&mut self, text: &str) -> Result<()> {
        self.raw("\"")?;
        for character in text.chars() {
            match character {
                '"' => self.raw("\\\"")?,
                '\\' => self.raw("\\\\")?,
                '\n' => self.raw("\\n")?,
                '\r' => self.raw("\\r")?,
                '\t' => self.raw("\\t")?,
                c if c.is_control()
                    || matches!(c, '\u{061c}' | '\u{200b}'..='\u{200f}' |
                    '\u{2028}'..='\u{202e}' | '\u{2060}'..='\u{206f}' | '\u{feff}') =>
                {
                    for unit in c.encode_utf16(&mut [0; 2]) {
                        write!(self, "\\u{unit:04x}").map_err(|_| RenderError::OutputLimit)?;
                    }
                }
                c => {
                    self.raw(c.encode_utf8(&mut [0; 4]))?;
                }
            }
        }
        self.raw("\"")
    }
    pub(crate) fn number(&mut self, number: impl fmt::Display) -> Result<()> {
        write!(self, "{number}").map_err(|_| RenderError::OutputLimit)
    }
    pub(crate) fn boolean(&mut self, value: bool) -> Result<()> {
        self.raw(if value { "true" } else { "false" })
    }
    fn separator(&mut self) -> Result<()> {
        let first = self
            .first
            .last_mut()
            .ok_or(RenderError::InvalidRecord("JSON container"))?;
        let needs_comma = !*first;
        *first = false;
        if needs_comma {
            self.raw(",")?;
        }
        if self.pretty {
            self.raw("\n")?;
            for _ in 0..self.depth {
                self.raw("  ")?;
            }
        }
        Ok(())
    }
    fn container(
        &mut self,
        open: &str,
        close: &str,
        body: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        self.raw(open)?;
        self.first.push(true);
        self.depth += 1;
        body(self)?;
        self.depth -= 1;
        let empty = self
            .first
            .pop()
            .ok_or(RenderError::InvalidRecord("JSON container"))?;
        if self.pretty && !empty {
            self.raw("\n")?;
            for _ in 0..self.depth {
                self.raw("  ")?;
            }
        }
        self.raw(close)
    }
    pub(crate) fn object(&mut self, body: impl FnOnce(&mut Self) -> Result<()>) -> Result<()> {
        self.container("{", "}", body)
    }
    pub(crate) fn array(&mut self, body: impl FnOnce(&mut Self) -> Result<()>) -> Result<()> {
        self.container("[", "]", body)
    }
    pub(crate) fn field(
        &mut self,
        name: &str,
        body: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        self.separator()?;
        self.string(name)?;
        self.raw(if self.pretty { ": " } else { ":" })?;
        body(self)
    }
    pub(crate) fn item(&mut self, body: impl FnOnce(&mut Self) -> Result<()>) -> Result<()> {
        self.separator()?;
        body(self)
    }
    pub(crate) fn text(&mut self, name: &str, value: &str) -> Result<()> {
        self.field(name, |j| j.string(value))
    }
    pub(crate) fn count(&mut self, name: &str, value: impl fmt::Display) -> Result<()> {
        self.field(name, |j| j.number(value))
    }
    pub(crate) fn flag(&mut self, name: &str, value: bool) -> Result<()> {
        self.field(name, |j| j.boolean(value))
    }
}
impl Write for Json {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.raw(text).map_err(|_| fmt::Error)
    }
}

impl Json {
    pub(crate) fn decimal(&mut self, name: &str, number: impl fmt::Display) -> Result<()> {
        self.field(name, |j| {
            j.raw("\"")?;
            j.number(number)?;
            j.raw("\"")
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Json, RenderError, Result};

    fn encoded(limit: usize, pretty: bool, payload: &str) -> Result<Vec<u8>> {
        let mut json = Json::new(limit, pretty);
        json.object(|json| json.text("value", payload))?;
        Ok(json.finish())
    }

    #[test]
    fn escaped_utf8_has_an_exact_complete_buffer_boundary()
    -> std::result::Result<(), Box<dyn std::error::Error>> {
        let payload = "é\\\"\u{1b}\n\u{202e}";
        for pretty in [false, true] {
            let full = encoded(4096, pretty, payload)?;
            let decoded: serde_json::Value = serde_json::from_slice(&full)?;
            assert_eq!(decoded["value"], payload);
            let exact = encoded(full.len(), pretty, payload)?;
            assert_eq!(
                serde_json::from_slice::<serde_json::Value>(&exact)?,
                decoded
            );
            assert_eq!(
                encoded(full.len() - 1, pretty, payload),
                Err(RenderError::OutputLimit)
            );
            assert_eq!(encoded(0, pretty, payload), Err(RenderError::OutputLimit));
        }
        Ok(())
    }
}
