use crate::InvariantError;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclId(usize);
impl DeclId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ValueId(usize);
impl ValueId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomId(usize);
impl AtomId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(usize);
impl NodeId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OriginId(usize);
impl OriginId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SetId(usize);
impl SetId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BinderId(usize);
impl BinderId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QuantifierId(usize);
impl QuantifierId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CheckId(usize);
impl CheckId {
    pub(crate) fn at(index: usize) -> Self {
        Self(index)
    }
    pub fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceSpan {
    start: usize,
    end: usize,
}
impl SourceSpan {
    pub fn checked(source: &str, start: usize, end: usize) -> Result<Self, InvariantError> {
        if start > end
            || end > source.len()
            || !source.is_char_boundary(start)
            || !source.is_char_boundary(end)
        {
            return Err(InvariantError::InvalidSpan);
        }
        Ok(Self { start, end })
    }
    pub fn start(self) -> usize {
        self.start
    }
    pub fn end(self) -> usize {
        self.end
    }
    pub fn cover(self, other: Self, source: &str) -> Result<Self, InvariantError> {
        Self::checked(source, self.start.min(other.start), self.end.max(other.end))
    }
}
