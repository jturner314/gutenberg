use context;
use errors::{Result, ResultExt};
use pest::Parser;
use pest::inputs::Input;
use pest::iterators::Pair;
use std::borrow::Cow;
use tera::{self, to_value, Tera, Value};

#[cfg(debug_assertions)]
const _GRAMMAR: &'static str = include_str!("short_code.pest");

#[derive(Parser)]
#[grammar = "short_code.pest"]
pub struct ShortCodeParser;

/// Debug assertion that the value matches the pattern.
macro_rules! debug_assert_match {
    ($pattern:pat, $value:expr) => {
        if cfg!(debug_assertions) {
            #[allow(unreachable_patterns)]
            match $value {
                $pattern => {},
                _ => panic!("\
assertion failed: `(value matches pattern)`
 pattern: `{}`,
   value: `{:?}`", stringify!($pattern), $value),
            }
        }
    }
}

/// Extracts inner pairs matching the specified rules from the given pair.
///
/// Uses `debug_assert_match!` to assert that the inner pairs match the
/// specified rules. Uses `debug_assert_match!` to verify that there are no
/// additional pairs unless there is a `..` after the patterns (e.g.
/// `parse_pairs_as!(pair.into_inner(), (Rule::foo, Rule::bar | Rule::baz), ..)`).
///
/// For example:
///
/// ```rust,ignore
/// parse_pairs_as!(pair.into_inner(), (Rule::foo, Rule::bar))
/// ```
///
/// becomes
///
/// ```rust,ignore
/// {
///     let mut iter = &mut pair.into_inner();
///     let out = (
///         {
///             let tmp = iter.next().unwrap();
///             debug_assert_match!(Rule::foo, tmp.as_rule()),
///             tmp
///         },
///         {
///             let tmp = iter.next().unwrap();
///             debug_assert_match!(Rule::bar, tmp.as_rule()),
///             tmp
///         },
///     );
///     debug_assert_match!(None, iter.next());
///     out
/// }
/// ```
macro_rules! parse_pairs_as {
    ($pair:expr, ($($rules:pat),*)) => {
        parse_pairs_as!($pair, ($($rules),*,))
    };
    ($pair:expr, ($($rules:pat),*), ..) => {
        parse_pairs_as!($pair, ($($rules),*,), ..)
    };
    ($pair:expr, ($($rules:pat),*,)) => {
        {
            let iter = &mut $pair;
            let out = parse_pairs_as!(@recur iter, (), ($($rules),*,));
            debug_assert_match!(None, iter.next());
            out
        }
    };
    ($pair:expr, ($($rules:pat),*,), ..) => {
        {
            let iter = &mut $pair;
            parse_pairs_as!(@recur iter, (), ($($rules),*,))
        }
    };
    (@recur $iter:ident, (), ($head_rule:pat, $($remaining_rules:pat),*,)) => {
        parse_pairs_as!(@recur
            $iter,
            (
                {
                    let tmp = $iter.next().unwrap();
                    debug_assert_match!($head_rule, tmp.as_rule());
                    tmp
                },
            ),
            ($($remaining_rules),*,)
        )
    };
    (@recur
        $iter:ident,
        ($($processed:expr),*,),
        ($head_rule:pat, $($remaining_rules:pat),*,)
    ) => {
        parse_pairs_as!(@recur
            $iter,
            (
                $($processed),*,
                {
                    let tmp = $iter.next().unwrap();
                    debug_assert_match!($head_rule, tmp.as_rule());
                    tmp
                }
            ),
            ($($remaining_rules),*,)
        )
    };
    (@recur $iter:ident, (), ($head_rule:pat,)) => {
        (
            {
                let tmp = $iter.next().unwrap();
                debug_assert_match!($head_rule, tmp.as_rule());
                tmp
            },
        )
    };
    (@recur $iter:ident, ($($processed:expr),*,), ($head_rule:pat,)) => {
        (
            $($processed),*,
            {
                let tmp = $iter.next().unwrap();
                debug_assert_match!($head_rule, tmp.as_rule());
                tmp
            },
        )
    };
}

/// Parses a non-raw string literal (e.g. "text").
fn parse_string<I: Input>(string: Pair<Rule, I>) -> String {
    debug_assert_eq!(string.as_rule(), Rule::string);
    let (string_body,) = parse_pairs_as!(string.into_inner(), (Rule::string_body,));
    let mut out = String::new();
    for item in string_body.into_inner() {
        match item.as_rule() {
            Rule::non_escape => out.push_str(item.as_str()),
            Rule::escape => match item.as_str() {
                "\"" => out.push('"'),
                "\\" => out.push('\\'),
                "n" => out.push('\n'),
                "r" => out.push('\r'),
                "t" => out.push('\t'),
                "0" => out.push('\0'),
                s if s.starts_with('x') => out.push(
                    ::std::char::from_u32(u32::from_str_radix(&s[1..], 16).unwrap())
                        .expect(&format!("Escape is invalid char: \\{}", s)),
                ),
                s if s.starts_with('\n') => {}
                _ => unreachable!(),
            },
            Rule::unicode_escape => out.push(
                ::std::char::from_u32(u32::from_str_radix(&item.as_str(), 16).unwrap())
                    .expect(&format!("Escape is invalid char: \\u{{{}}}", item.as_str())),
            ),
            _ => unreachable!(),
        }
    }
    out
}

/// Parses a raw string literal (e.g. `r#"text"#`).
fn parse_raw_string<I: Input>(raw_string: Pair<Rule, I>) -> String {
    debug_assert_eq!(raw_string.as_rule(), Rule::raw_string);
    let (raw_string_body,) = parse_pairs_as!(raw_string.into_inner(), (Rule::raw_string_body,));
    raw_string_body.as_str().to_owned()
}

/// Parses a bool literal.
fn parse_bool<I: Input>(b: Pair<Rule, I>) -> bool {
    debug_assert_eq!(b.as_rule(), Rule::bool);
    match b.as_str() {
        "true" => true,
        "false" => false,
        _ => unreachable!(),
    }
}

/// Parses a float literal.
///
/// Note that this method is necessary because `str.parse::<f64>()` does not
/// allow `_` in the number literal.
fn parse_float<I: Input>(float: Pair<Rule, I>) -> f64 {
    fn push_dec_body<I: Input>(repr: &mut String, dec_body: Pair<Rule, I>) {
        for digit in dec_body.into_inner() {
            debug_assert_eq!(digit.as_rule(), Rule::dec_digit);
            repr.push_str(digit.as_str());
        }
    }
    debug_assert_eq!(float.as_rule(), Rule::float);
    let mut repr = String::new();
    for item in float.into_inner() {
        match item.as_rule() {
            Rule::neg_sign => repr.push('-'),
            Rule::dec_body => push_dec_body(&mut repr, item),
            Rule::dec_point => repr.push('.'),
            Rule::exponent => {
                repr.push('e');
                for sign_or_body in item.into_inner() {
                    match sign_or_body.as_rule() {
                        Rule::neg_sign => repr.push('-'),
                        Rule::dec_body => push_dec_body(&mut repr, sign_or_body),
                        _ => unreachable!(),
                    }
                }
            }
            _ => unreachable!(),
        }
    }
    repr.parse().unwrap()
}

/// Parses an integer literal.
fn parse_integer<I: Input>(integer: Pair<Rule, I>) -> i64 {
    fn parse_body<I: Input>(body: Pair<Rule, I>, digit_rule: Rule, radix: u32) -> i64 {
        let mut repr = String::new();
        for digit in body.into_inner() {
            debug_assert_eq!(digit.as_rule(), digit_rule);
            repr.push_str(digit.as_str());
        }
        i64::from_str_radix(&repr, radix).unwrap()
    }
    debug_assert_eq!(integer.as_rule(), Rule::integer);
    let mut neg = false;
    let mut body = None;
    for sign_or_body in integer.into_inner() {
        match sign_or_body.as_rule() {
            Rule::neg_sign => neg = true,
            Rule::dec_body => body = Some(parse_body(sign_or_body, Rule::dec_digit, 10)),
            Rule::bin_body => body = Some(parse_body(sign_or_body, Rule::bin_digit, 2)),
            Rule::oct_body => body = Some(parse_body(sign_or_body, Rule::oct_digit, 8)),
            Rule::hex_body => body = Some(parse_body(sign_or_body, Rule::hex_digit, 16)),
            _ => unreachable!(),
        }
    }
    if neg {
        -body.unwrap()
    } else {
        body.unwrap()
    }
}

/// Parses a literal value (string, bool, float, integer, etc.).
fn parse_literal<I: Input>(literal: Pair<Rule, I>) -> Value {
    debug_assert_eq!(literal.as_rule(), Rule::literal);
    let (lit,) = parse_pairs_as!(literal.into_inner(), (_,));
    match lit.as_rule() {
        Rule::string => to_value(parse_string(lit)),
        Rule::raw_string => to_value(parse_raw_string(lit)),
        Rule::bool => to_value(parse_bool(lit)),
        Rule::float => to_value(parse_float(lit)),
        Rule::integer => to_value(parse_integer(lit)),
        _ => unreachable!(),
    }.unwrap_or_else(|e| panic!("Failed to serialize literal: {}", e))
}

/// Parses the shortcode expression given the context of the surrounding scope.
///
/// Returns the name of the shortcode and the context for the inside of the
/// shortcode.
fn parse_shortcode_expr<I: Input>(
    shortcode_expr: Pair<Rule, I>,
    outer_context: &tera::Context,
) -> (Pair<Rule, I>, Cow<tera::Context>) {
    debug_assert_eq!(shortcode_expr.as_rule(), Rule::shortcode_expr);
    let mut new_context = Cow::Borrowed(outer_context);
    let mut inner = shortcode_expr.into_inner();
    let (name,) = parse_pairs_as!(inner, (Rule::ident,), ..);
    for arg in inner {
        debug_assert_eq!(arg.as_rule(), Rule::arg);
        let (key, literal) = parse_pairs_as!(arg.into_inner(), (Rule::ident, Rule::literal));
        new_context
            .to_mut()
            .add(key.as_str(), &parse_literal(literal));
    }
    (name, new_context)
}

/// Copied from `tera/src/context.rs`
trait ValueRender {
    fn render(&self) -> String;
}

/// Copied from `tera/src/context.rs`
impl ValueRender for Value {
    fn render(&self) -> String {
        match *self {
            Value::String(ref s) => s.clone(),
            Value::Number(ref i) => i.to_string(),
            Value::Bool(i) => i.to_string(),
            Value::Null => "".to_owned(),
            Value::Array(ref a) => {
                let mut buf = String::new();
                buf.push('[');
                for i in a.iter() {
                    buf.push_str(i.render().as_ref());
                    buf.push_str(", ");
                }
                buf.push(']');
                buf
            }
            Value::Object(_) => "[object]".to_owned(),
        }
    }
}

fn render_block_shortcode<I: Input>(
    block_shortcode: Pair<Rule, I>,
    outer_context: &tera::Context,
    tera: &Tera,
) -> Result<String> {
    debug_assert_eq!(block_shortcode.as_rule(), Rule::block_shortcode);
    let (shortcode_expr, body) = parse_pairs_as!(
        block_shortcode.into_inner(),
        (Rule::shortcode_expr, Rule::body)
    );
    let (name, mut context) = parse_shortcode_expr(shortcode_expr, &outer_context);
    {
        let body_str = render_body(body, &context, tera)?;
        context.to_mut().add("body", &body_str);
    }
    let tpl_name = format!("shortcodes/{}.html", name.as_str());
    tera.render(&tpl_name, &context)
        .chain_err(|| format!("Failed to render {} shortcode", name.as_str()))
}

fn render_inline_shortcode<I: Input>(
    inline_shortcode: Pair<Rule, I>,
    outer_context: &tera::Context,
    tera: &Tera,
) -> Result<String> {
    debug_assert_eq!(inline_shortcode.as_rule(), Rule::inline_shortcode);
    let (shortcode_expr,) = parse_pairs_as!(inline_shortcode.into_inner(), (Rule::shortcode_expr,));
    let (name, context) = parse_shortcode_expr(shortcode_expr, &outer_context);
    let tpl_name = format!("shortcodes/{}.html", name.as_str());
    tera.render(&tpl_name, &context)
        .chain_err(|| format!("Failed to render {} shortcode", name.as_str()))
}

fn render_body<I: Input>(
    body: Pair<Rule, I>,
    outer_context: &tera::Context,
    tera: &Tera,
) -> Result<String> {
    debug_assert_eq!(body.as_rule(), Rule::body);
    let mut out = String::new();
    for body_elem in body.into_inner() {
        match body_elem.as_rule() {
            Rule::block_shortcode => {
                out.push_str(&render_block_shortcode(body_elem, outer_context, tera)?);
            }
            Rule::inline_literal => {
                let (literal,) = parse_pairs_as!(body_elem.into_inner(), (Rule::literal,));
                out.push_str(&parse_literal(literal).render());
            }
            Rule::inline_shortcode => {
                out.push_str(&render_inline_shortcode(body_elem, outer_context, tera)?);
            }
            Rule::text => out.push_str(body_elem.as_str()),
            _ => unreachable!(),
        }
    }
    Ok(out)
}

pub fn render_all(input: &str, context: &context::Context) -> Result<String> {
    let mut parsed = ShortCodeParser::parse_str(Rule::start, input)
        .map_err(|e| format!("Failed parsing content for shortcodes:\n{}", e))?;
    let (start,) = parse_pairs_as!(parsed, (Rule::start,));
    let (body,) = parse_pairs_as!(start.into_inner(), (Rule::body,));
    render_body(body, &tera::Context::new(), context.tera)
}

#[cfg(test)]
mod tests {
    use pest::inputs::StrInput;
    use super::*;

    fn parse_shortcode_expr_from_str<'a, 'b>(
        input: &'a str,
        outer_context: &'b tera::Context,
    ) -> (Pair<Rule, StrInput<'a>>, Cow<'b, tera::Context>) {
        let mut parsed = ShortCodeParser::parse_str(Rule::shortcode_expr, input)
            .unwrap_or_else(|err| panic!("failed to parse: {}", err));
        let (shortcode_expr,) = parse_pairs_as!(parsed, (Rule::shortcode_expr,));
        let (name, context) = parse_shortcode_expr(shortcode_expr, outer_context);
        (name, context)
    }

    #[test]
    fn can_parse_simple_shortcode_expr_no_arg() {
        let outer_context = tera::Context::new();
        let (name, args) = parse_shortcode_expr_from_str(r#"basic()"#, &outer_context);
        let context = tera::Context::new();
        assert_eq!(name.as_str(), "basic");
        assert_eq!(*args, context);
    }

    #[test]
    fn can_parse_simple_shortcode_expr_one_arg() {
        let outer_context = tera::Context::new();
        let (name, args) =
            parse_shortcode_expr_from_str(r#"youtube(id="w7Ft2ymGmfc")"#, &outer_context);
        let mut context = tera::Context::new();
        context.add("id", "w7Ft2ymGmfc");
        assert_eq!(name.as_str(), "youtube");
        assert_eq!(*args, context);
    }

    #[test]
    fn can_parse_simple_shortcode_expr_several_arg() {
        let mut outer_context = tera::Context::new();
        let (name, args) = parse_shortcode_expr_from_str(
            r#"youtube(id="w7Ft2ymGmfc", autoplay=true)"#,
            &outer_context,
        );
        let mut context = tera::Context::new();
        context.add("id", "w7Ft2ymGmfc");
        context.add("autoplay", &true);
        assert_eq!(name.as_str(), "youtube");
        assert_eq!(*args, context);
    }

    #[test]
    fn can_parse_shortcode_expr_string() {
        let mut outer_context = tera::Context::new();
        let (name, args) = parse_shortcode_expr_from_str(
            r#"test(
            normal="foo bar", with_comma="foo,bar", with_paren="foo) %}",
            escapes="foo\ta\"\\\n\r\t\0\
            \x7f\

\u{fff}",
            multiline="foo
bar")"#,
            &outer_context,
        );
        let mut context = tera::Context::new();
        context.add("normal", "foo bar");
        context.add("with_comma", "foo,bar");
        context.add("with_paren", "foo) %}");
        context.add(
            "escapes",
            "foo\ta\"\\\n\r\t\0\
             \x7f\

\u{fff}",
        );
        context.add(
            "multiline",
            "foo
bar",
        );
        assert_eq!(name.as_str(), "test");
        assert_eq!(*args, context);
    }

    #[test]
    fn can_parse_shortcode_expr_raw_string() {
        let mut outer_context = tera::Context::new();
        let (name, args) = parse_shortcode_expr_from_str(
            r###"test(
            normal=r"foo#\tbar", with_pound=r#"foo"bar"#,
            with_multi_pound=r##"foo"#\tbar"##,
            multiline=r"foo\
bar")"###,
            &outer_context,
        );
        let mut context = tera::Context::new();
        context.add("normal", r"foo#\tbar");
        context.add("with_pound", r#"foo"bar"#);
        context.add("with_multi_pound", r##"foo"#\tbar"##);
        context.add(
            "multiline",
            r"foo\
bar",
        );
        assert_eq!(name.as_str(), "test");
        assert_eq!(*args, context);
    }

    #[test]
    fn can_parse_shortcode_expr_bool() {
        let mut outer_context = tera::Context::new();
        let (name, args) =
            parse_shortcode_expr_from_str(r#"test(true=true, false=false)"#, &outer_context);
        let mut context = tera::Context::new();
        context.add("true", &true);
        context.add("false", &false);
        assert_eq!(name.as_str(), "test");
        assert_eq!(*args, context);
    }

    #[test]
    fn can_parse_shortcode_expr_float() {
        let mut outer_context = tera::Context::new();
        let (name, args) = parse_shortcode_expr_from_str(
            r#"test(
            float=42.0, neg=-4_2., dec=.4_2,
            exp=4_2e3, pos_exp=42e+3, neg_exp=-42.0e-3)"#,
            &outer_context,
        );
        let mut context = tera::Context::new();
        context.add("float", &42.0);
        context.add("neg", &-4_2.);
        context.add("dec", &0.4_2);
        context.add("exp", &4_2e3);
        context.add("pos_exp", &42e+3);
        context.add("neg_exp", &-42.0e-3);
        assert_eq!(name.as_str(), "test");
        assert_eq!(*args, context);
    }

    #[test]
    fn can_parse_shortcode_expr_integer() {
        let mut outer_context = tera::Context::new();
        let (name, args) = parse_shortcode_expr_from_str(
            r#"test(
            int=42, neg=-4_2, bin=0b1010, neg_bin=-0b10_10,
            oct=0o77, neg_oct=-0o7_7, hex=0xff, neg_hex=-0xf_f)"#,
            &outer_context,
        );
        let mut context = tera::Context::new();
        context.add("int", &42);
        context.add("neg", &-4_2);
        context.add("bin", &0b1010);
        context.add("neg_bin", &-0b10_10);
        context.add("oct", &0o77);
        context.add("neg_oct", &-0o7_7);
        context.add("hex", &0xff);
        context.add("neg_hex", &-0xf_f);
        assert_eq!(name.as_str(), "test");
        assert_eq!(*args, context);
    }
}
