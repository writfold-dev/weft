use super::{Kind, lex};
use std::borrow::Cow;
use weft_domain::{Code, Limits, Phase};

#[test]
fn unicode_strings_keep_exact_byte_spans_and_borrow() -> Result<(), String> {
    let source = "\"α🙂\" name";
    let tokens = lex(source, &Limits::default()).map_err(|error| format!("{error:?}"))?;
    let string = tokens.first().ok_or("missing string token")?;
    assert_eq!((string.span.start(), string.span.end()), (0, 8));
    assert!(matches!(&string.text, Some(Cow::Borrowed("α🙂"))));
    let name = tokens.get(1).ok_or("missing identifier token")?;
    assert_eq!((name.span.start(), name.span.end()), (9, 13));
    assert_eq!(
        name.lexeme.as_ptr(),
        source.get(9..13).ok_or("source slice")?.as_ptr()
    );
    Ok(())
}

#[test]
fn supported_escapes_decode_once_without_normalization() -> Result<(), String> {
    let source = r#""é\n🙂\r\t\"\\""#;
    let tokens = lex(source, &Limits::default()).map_err(|error| format!("{error:?}"))?;
    let token = tokens.first().ok_or("missing string token")?;
    assert!(matches!(&token.text, Some(Cow::Owned(value)) if value == "é\n🙂\r\t\"\\"));
    assert_eq!(token.lexeme, source);
    assert_eq!(token.span.end(), source.len());
    Ok(())
}

#[test]
fn maximal_munch_and_keyword_boundaries_are_distinct() -> Result<(), String> {
    let source = "android forallx forall _x9 ... := == != . : =";
    let tokens = lex(source, &Limits::default()).map_err(|error| format!("{error:?}"))?;
    let kinds: Vec<_> = tokens.iter().map(|token| token.kind).collect();
    assert_eq!(
        kinds,
        [
            Kind::Ident,
            Kind::Ident,
            Kind::Keyword("forall"),
            Kind::Ident,
            Kind::Spread,
            Kind::Bind,
            Kind::Equal,
            Kind::NotEqual,
            Kind::Dot,
            Kind::Colon,
            Kind::Assign
        ]
    );
    Ok(())
}

#[test]
fn comments_respect_strings_and_line_endings() -> Result<(), String> {
    let tokens = lex("// ignored\r\n\"//text\" // eof", &Limits::default())
        .map_err(|error| format!("{error:?}"))?;
    assert_eq!(tokens.len(), 1);
    assert_eq!(
        tokens.first().and_then(|token| token.text.as_deref()),
        Some("//text")
    );
    for source in ["\r", "// comment\r", "// comment\rx\n"] {
        let error = lex(source, &Limits::default())
            .err()
            .ok_or("accepted isolated CR")?;
        assert_eq!(error.code, Code::InvalidCharacter);
        let span = error.primary.ok_or("missing CR span")?;
        assert_eq!(source.get(span.start()..span.end()), Some("\r"));
    }
    Ok(())
}

#[test]
fn malformed_strings_and_unicode_tokens_are_diagnostic() -> Result<(), String> {
    let cases = [
        ("\"\\u1234\"", Code::InvalidEscape),
        ("\"\\q\"", Code::InvalidEscape),
        ("\"line\nnext\"", Code::InvalidCharacter),
        ("\"\u{85}\"", Code::InvalidCharacter),
        ("\"\0\"", Code::InvalidCharacter),
        ("\"open", Code::UnterminatedString),
        ("\"trailing\\", Code::UnterminatedString),
        ("β", Code::InvalidCharacter),
    ];
    for (source, code) in cases {
        let error = lex(source, &Limits::default())
            .err()
            .ok_or("accepted malformed token")?;
        assert_eq!(error.code, code, "{source:?}");
        assert_eq!(error.phase, Phase::Lex);
        let span = error.primary.ok_or("missing token span")?;
        assert!(source.is_char_boundary(span.start()) && source.is_char_boundary(span.end()));
        assert!(error.expected.is_some() && error.actual.is_some() && error.help.is_some());
    }
    Ok(())
}

#[test]
fn numbers_have_canonical_boundaries_without_machine_integer_conversion() -> Result<(), String> {
    for source in ["00", "012", "12abc", "0x10", "1e9", "1_name", "1β"] {
        let error = lex(source, &Limits::default())
            .err()
            .ok_or("accepted malformed natural")?;
        assert_eq!(error.code, Code::InvalidNatural, "{source}");
    }
    let number = "1234567890123456789012345678901234567890";
    let tokens = lex(number, &Limits::default()).map_err(|error| format!("{error:?}"))?;
    assert_eq!(tokens.first().map(|token| token.lexeme), Some(number));
    Ok(())
}

#[test]
fn lexical_budgets_accept_exact_edges_and_refuse_next_unit() -> Result<(), String> {
    let mut limits = Limits {
        source_bytes: 3,
        tokens: 1,
        natural_digits: 3,
        ..Limits::default()
    };
    assert!(lex("123", &limits).is_ok());
    for source in ["1234", "1 2"] {
        let error = lex(source, &limits)
            .err()
            .ok_or("accepted excessive lexical input")?;
        assert_eq!(error.code, Code::LimitExceeded);
    }
    limits.source_bytes = 10;
    limits.natural_digits = 2;
    assert_eq!(
        lex("123", &limits)
            .err()
            .ok_or("accepted excessive digits")?
            .code,
        Code::LimitExceeded
    );
    limits.natural_digits = 0;
    assert_eq!(
        lex("0", &limits)
            .err()
            .ok_or("accepted a digit with zero budget")?
            .code,
        Code::LimitExceeded
    );
    limits.tokens = 0;
    assert!(lex(" //empty", &limits).is_ok());
    assert_eq!(
        lex("x", &limits)
            .err()
            .ok_or("accepted token with zero budget")?
            .code,
        Code::LimitExceeded
    );
    Ok(())
}
