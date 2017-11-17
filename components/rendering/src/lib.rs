extern crate tera;
extern crate syntect;
extern crate pest;
#[macro_use]
extern crate pest_derive;
extern crate pulldown_cmark;
extern crate slug;
#[macro_use]
extern crate serde_derive;
extern crate serde;

extern crate errors;
extern crate front_matter;
extern crate highlighting;
extern crate utils;

#[cfg(test)]
extern crate templates;

mod context;
mod markdown;
mod short_code;
mod table_of_contents;

pub use context::Context;
pub use markdown::markdown_to_html;
pub use short_code::render_all as render_shortcodes;
pub use table_of_contents::Header;
