use crate::InvariantError;

// Equality is the only natural operation in this fragment. Canonical decimal
// storage is exact at arbitrary precision and needs neither arithmetic nor
// repeated decimal formatting in reports.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Natural {
    digits: Box<str>,
}
impl Natural {
    pub fn parse(digits: &str) -> Result<Self, InvariantError> {
        if digits.is_empty()
            || !digits.bytes().all(|b| b.is_ascii_digit())
            || (digits.len() > 1 && digits.starts_with('0'))
        {
            return Err(InvariantError::InvalidNatural);
        }
        Ok(Self {
            digits: digits.into(),
        })
    }
    pub fn as_str(&self) -> &str {
        &self.digits
    }
}

// A mathematical captured identity, not a Writfold wire descriptor or receipt.
// Source citation strings cannot construct this through the local profile.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IdentityValue {
    kind: Box<str>,
    realm: Box<str>,
    body: Box<str>,
}
impl IdentityValue {
    pub fn checked(kind: String, realm: String, body: String) -> Result<Self, InvariantError> {
        if kind.is_empty() || realm.is_empty() || body.is_empty() {
            return Err(InvariantError::EmptyIdentityComponent);
        }
        Ok(Self {
            kind: kind.into_boxed_str(),
            realm: realm.into_boxed_str(),
            body: body.into_boxed_str(),
        })
    }
    pub fn kind(&self) -> &str {
        &self.kind
    }
    pub fn realm(&self) -> &str {
        &self.realm
    }
    pub fn body(&self) -> &str {
        &self.body
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Scalar {
    Boolean(bool),
    Natural(Natural),
    Text(String),
    Identity(IdentityValue),
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarType {
    Boolean,
    Natural,
    Text,
    Identity { kind: String, realm: String },
}
impl Scalar {
    pub fn scalar_type(&self) -> ScalarType {
        match self {
            Self::Boolean(_) => ScalarType::Boolean,
            Self::Natural(_) => ScalarType::Natural,
            Self::Text(_) => ScalarType::Text,
            Self::Identity(value) => ScalarType::Identity {
                kind: value.kind().into(),
                realm: value.realm().into(),
            },
        }
    }
    pub fn has_type(&self, ty: &ScalarType) -> bool {
        match (self, ty) {
            (Self::Boolean(_), ScalarType::Boolean)
            | (Self::Natural(_), ScalarType::Natural)
            | (Self::Text(_), ScalarType::Text) => true,
            (Self::Identity(value), ScalarType::Identity { kind, realm }) => {
                value.kind() == kind && value.realm() == realm
            }
            _ => false,
        }
    }
}
