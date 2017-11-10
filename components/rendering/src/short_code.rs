use std::collections::HashMap;

use regex::Regex;
use tera::{Tera, Context, Value, to_value};

use errors::{Result, ResultExt};

lazy_static!{
    pub static ref SHORTCODE_RE: Regex = Regex::new(r#"(?x)
      \{(?:%|\{)                # opening {{ or {%
      \s+
      (?P<name>                 # shortcode name
        [[:word:]]+?
      )
      \((?P<arg_list>           # start of arg list
        (?:
          [[:word:]]+?          # argument name
          =
          (?:                   # argument value
            "[^"]*?" |          # string
            true | false |      # bool
            (?:                 # float
              [+-]?
              (?:
                [0-9]+\.[0-9]*(?:[eE][+-]?[0-9]+)? |
                [0-9]*\.[0-9]+(?:[eE][+-]?[0-9]+)? |
                [0-9]+[eE][+-]?[0-9]+ |
                NaN
              )
            ) |
            [+-]?[0-9]+         # integer
          )
          ,\s*                  # separating comma
        )*
        [[:word:]]+?            # argument name
        =
        (?:                     # argument value
          "[^"]*?" |            # string
          true | false |        # bool
          (?:                   # float
            [+-]?
            (?:
              [0-9]+\.[0-9]*(?:[eE][+-]?[0-9]+)? |
              [0-9]*\.[0-9]+(?:[eE][+-]?[0-9]+)? |
              [0-9]+[eE][+-]?[0-9]+ |
              NaN
            )
          ) |
          [+-]?[0-9]+           # integer
        )
      )?\)                      # end of arg list
      \s+
      (?:%|\})\}                # closing }} or %}
    "#).unwrap();

    pub static ref ARG_NAME_VALUE_RE: Regex = Regex::new(r#"(?x)
      (?P<name>           # argument name
        [[:word:]]+?
      )
      =
      (?:                 # argument value
        (?:"(?P<string>   # string
          [^"]*?
        )") |
        (?P<true>         # true (bool)
          true
        ) |
        (?P<false>        # false (bool)
          false
        ) |
        (?P<float>        # float
          [+-]?
          (?:
            [0-9]+\.[0-9]*(?:[eE][+-]?[0-9]+)? |
            [0-9]*\.[0-9]+(?:[eE][+-]?[0-9]+)? |
            [0-9]+[eE][+-]?[0-9]+ |
            NaN
          )
        ) |
        (?P<integer>      # integer
          [+-]?[0-9]+
        )
      )
      (?:,\s*|\z)         # separating comma or end of text
    "#).unwrap();
}

/// A shortcode that has a body
/// Called by having some content like {% ... %} body {% end %}
/// We need the struct to hold the data while we're processing the markdown
#[derive(Debug)]
pub struct ShortCode {
    name: String,
    args: HashMap<String, Value>,
    body: String,
}

impl ShortCode {
    pub fn new(name: &str, args: HashMap<String, Value>) -> ShortCode {
        ShortCode {
            name: name.to_string(),
            args,
            body: String::new(),
        }
    }

    pub fn append(&mut self, text: &str) {
        self.body.push_str(text)
    }

    pub fn render(&self, tera: &Tera) -> Result<String> {
        let mut context = Context::new();
        for (key, value) in &self.args {
            context.add(key, value);
        }
        context.add("body", &self.body);
        let tpl_name = format!("shortcodes/{}.html", self.name);
        tera.render(&tpl_name, &context)
            .chain_err(|| format!("Failed to render {} shortcode", self.name))
    }
}

/// Parse a shortcode (not including the body)
pub fn parse_shortcode(input: &str) -> (String, HashMap<String, Value>) {
    let mut args = HashMap::new();
    let caps = SHORTCODE_RE.captures(input).unwrap();
    let name = caps.name("name").unwrap().as_str();

    if let Some(arg_list) = caps.name("arg_list") {
        let mut remaining = arg_list.as_str();
        while !remaining.is_empty() {
            let caps = ARG_NAME_VALUE_RE.captures(remaining).unwrap();
            let arg_name = caps.name("name").unwrap().as_str().to_owned();
            if let Some(mat) = caps.name("string") {
                args.insert(arg_name, to_value(mat.as_str()).unwrap());
            } else if let Some(_) = caps.name("true") {
                args.insert(arg_name, to_value(true).unwrap());
            } else if let Some(_) = caps.name("false") {
                args.insert(arg_name, to_value(false).unwrap());
            } else if let Some(mat) = caps.name("float") {
                let num: f64 = mat.as_str().parse().unwrap();
                args.insert(arg_name, to_value(num).unwrap());
            } else if let Some(mat) = caps.name("integer") {
                let num: i64 = mat.as_str().parse().unwrap();
                args.insert(arg_name, to_value(num).unwrap());
            } else {
                unreachable!();
            }
            // Remove this arg from the remaining text.
            remaining = &remaining[caps.get(0).unwrap().end()..];
        }
    }

    (name.to_string(), args)
}

/// Renders a shortcode or return an error
pub fn render_simple_shortcode(tera: &Tera, name: &str, args: &HashMap<String, Value>) -> Result<String> {
    let mut context = Context::new();
    for (key, value) in args.iter() {
        context.add(key, value);
    }
    let tpl_name = format!("shortcodes/{}.html", name);

    tera.render(&tpl_name, &context).chain_err(|| format!("Failed to render {} shortcode", name))
}


#[cfg(test)]
mod tests {
    use super::{parse_shortcode, SHORTCODE_RE};

    #[test]
    fn can_match_all_kinds_of_shortcode() {
        let inputs = vec![
            "{{ basic() }}",
            "{{ basic(ho=1) }}",
            "{{ basic(ho=\"hey\") }}",
            "{{ basic(ho=\"hey_underscore\") }}",
            "{{ basic(ho=\"hey-dash\") }}",
            "{% basic(ho=\"hey-dash\") %}",
            "{% basic(ho=\"hey_underscore\") %}",
            "{% basic() %}",
            "{% quo_te(author=\"Bob\") %}",
            "{{ quo_te(author=\"Bob\") }}",
        ];

        for i in inputs {
            println!("{}", i);
            assert!(SHORTCODE_RE.is_match(i));
        }
    }

    #[test]
    fn can_parse_simple_shortcode_no_arg() {
        let (name, args) = parse_shortcode(r#"{{ basic() }}"#);
        assert_eq!(name, "basic");
        assert!(args.is_empty());
    }

    #[test]
    fn can_parse_simple_shortcode_one_arg() {
        let (name, args) = parse_shortcode(r#"{{ youtube(id="w7Ft2ymGmfc") }}"#);
        assert_eq!(name, "youtube");
        assert_eq!(args["id"], "w7Ft2ymGmfc");
    }

    #[test]
    fn can_parse_simple_shortcode_several_arg() {
        let (name, args) = parse_shortcode(r#"{{ youtube(id="w7Ft2ymGmfc", autoplay=true) }}"#);
        assert_eq!(name, "youtube");
        assert_eq!(args["id"], "w7Ft2ymGmfc");
        assert_eq!(args["autoplay"], true);
    }

    #[test]
    fn can_parse_block_shortcode_several_arg() {
        let (name, args) = parse_shortcode(r#"{% youtube(id="w7Ft2ymGmfc", autoplay=true) %}"#);
        assert_eq!(name, "youtube");
        assert_eq!(args["id"], "w7Ft2ymGmfc");
        assert_eq!(args["autoplay"], true);
    }

    #[test]
    fn can_parse_shortcode_float() {
        let (name, args) = parse_shortcode("{% test(\
            float=42.0, neg=-42., pos=+0.42, dec=.42, \
            exp=42e3, pos_exp=+42e+3, neg_exp=-42.0e-3, \
            nan=NaN, autoplay=true\
        ) %}");
        assert_eq!(name, "test");
        assert_eq!(args["float"], 42.0);
        assert_eq!(args["neg"], -42.);
        assert_eq!(args["pos"], 0.42);
        assert_eq!(args["dec"], 0.42);
        assert_eq!(args["exp"], 42e3);
        assert_eq!(args["pos_exp"], 42e+3);
        assert_eq!(args["neg_exp"], -42.0e-3);
        assert!(args["nan"].is_null());
        assert_eq!(args["autoplay"], true);
    }

    #[test]
    fn can_parse_shortcode_integer() {
        let (name, args) = parse_shortcode("{% test(int=42, pos=+42, neg=-42, autoplay=true) %}");
        assert_eq!(name, "test");
        assert_eq!(args["int"], 42);
        assert_eq!(args["pos"], 42);
        assert_eq!(args["neg"], -42);
        assert_eq!(args["autoplay"], true);
    }

    #[test]
    fn can_parse_shortcode_string_with_comma() {
        let (name, args) = parse_shortcode(r#"{% test(id="foo,bar") %}"#);
        assert_eq!(name, "test");
        assert_eq!(args["id"], "foo,bar");
    }

    #[test]
    fn can_parse_shortcode_string_with_closing_paren_brace() {
        let (name, args) = parse_shortcode(r#"{% test(id="foo) %}") %}"#);
        assert_eq!(name, "test");
        assert_eq!(args["id"], "foo) %}");
    }
}
