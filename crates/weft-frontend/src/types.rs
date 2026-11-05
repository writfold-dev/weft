use weft_domain::{Code, Diagnostic, Phase, ScalarType, SourceSpan};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TypeVar(usize);

#[derive(Default)]
pub(crate) struct Types {
    entries: Vec<Entry>,
}
struct Entry {
    parent: TypeVar,
    concrete: Option<ScalarType>,
    rank: usize,
}
impl Types {
    pub fn fresh(&mut self, concrete: Option<ScalarType>) -> TypeVar {
        let id = TypeVar(self.entries.len());
        self.entries.push(Entry {
            parent: id,
            concrete,
            rank: 0,
        });
        id
    }
    fn root(&self, mut id: TypeVar) -> Option<TypeVar> {
        loop {
            let entry = self.entries.get(id.0)?;
            if entry.parent == id {
                return Some(id);
            }
            id = entry.parent;
        }
    }
    pub fn concrete(&self, id: TypeVar) -> Option<&ScalarType> {
        self.root(id)
            .and_then(|root| self.entries.get(root.0))
            .and_then(|entry| entry.concrete.as_ref())
    }
    pub fn unify(&mut self, a: TypeVar, b: TypeVar, span: SourceSpan) -> Result<(), Diagnostic> {
        let invalid = || {
            Diagnostic::new(
                Code::InvalidProgram,
                Phase::Type,
                "invalid type variable",
                Some(span),
            )
        };
        let a = self.root(a).ok_or_else(invalid)?;
        let b = self.root(b).ok_or_else(invalid)?;
        if a == b {
            return Ok(());
        }
        let left = self.entries.get(a.0).ok_or_else(invalid)?.concrete.clone();
        let right = self.entries.get(b.0).ok_or_else(invalid)?.concrete.clone();
        if let (Some(left), Some(right)) = (&left, &right)
            && left != right
        {
            let mut diagnostic = Diagnostic::new(
                Code::TypeMismatch,
                Phase::Type,
                "scalar types differ; implicit coercion is not supported",
                Some(span),
            );
            diagnostic.expected = Some(format!("{left:?}").into_boxed_str());
            diagnostic.actual = Some(format!("{right:?}").into_boxed_str());
            diagnostic.help = Some("Use values with the same exact scalar type.".into());
            return Err(diagnostic);
        }
        let rank_a = self.entries.get(a.0).ok_or_else(invalid)?.rank;
        let rank_b = self.entries.get(b.0).ok_or_else(invalid)?.rank;
        let (parent, child) = if rank_a < rank_b { (b, a) } else { (a, b) };
        self.entries.get_mut(child.0).ok_or_else(invalid)?.parent = parent;
        let entry = self.entries.get_mut(parent.0).ok_or_else(invalid)?;
        entry.concrete = left.or(right);
        if rank_a == rank_b {
            entry.rank = entry.rank.checked_add(1).ok_or_else(invalid)?;
        }
        Ok(())
    }
}
