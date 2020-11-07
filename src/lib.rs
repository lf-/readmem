//! A library for reading in Verilog $readmemb/$readmemh files formatted per
//! IEEE Std. 1364-2005, §17.2.9

use std::str::FromStr;

use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("syntax error")]
    ParseError(#[from] pest::error::Error<Rule>),
    #[error("we didn't successfully parse a top level syntax object")]
    ParseFailure,
    #[error("numeric format error")]
    NumericFormatError(#[from] std::num::ParseIntError),
}

/// The type of content contained in a file to be read.
pub enum ContentType {
    /// The file is compatible with $readmemh and contains hex values
    Hex,
    /// The file is compatible with $readmemb and contains binary values
    Binary,
}

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct ReadmemParser;

#[derive(Debug)]
enum Item<I> {
    Address(usize),
    Number(I),
}

/// A trait implemented on unsigned numeric types to allow us to be polymorphic
/// over them, supporting any storage type.
#[doc(hidden)]
pub trait Integral: Sized {
    fn from_str_radix(src: &str, radix: u32) -> Result<Self, std::num::ParseIntError>;
    fn zero() -> Self;
}

macro_rules! integrate {
    ($t:ty) => {
        impl Integral for $t {
            fn from_str_radix(src: &str, radix: u32) -> Result<Self, std::num::ParseIntError> {
                <$t>::from_str_radix(src, radix)
            }
            fn zero() -> Self {
                0
            }
        }
    };
}

integrate!(u8);
integrate!(u16);
integrate!(u32);
integrate!(u64);
integrate!(u128);

/// Parse a `Pair` into an AST `Item`.
fn parse_value<I>(pair: Pair<Rule>) -> Result<Item<I>, Error>
where
    I: Integral,
{
    let is_zx = |c| c == 'x' || c == 'z' || c == 'X' || c == 'Z';
    Ok(match pair.as_rule() {
        Rule::addr => Item::Address(usize::from_str_radix(&pair.as_str()[1..], 16)?),
        Rule::hexnum => {
            let without_underscore = pair.as_str().replace("_", "");
            let without_zx = without_underscore.replace(is_zx, "0");
            Item::Number(Integral::from_str_radix(&without_zx, 16)?)
        }
        Rule::binnum => {
            let without_underscore = pair.as_str().replace("_", "");
            let without_zx = without_underscore.replace(is_zx, "0");
            Item::Number(Integral::from_str_radix(&without_zx, 2)?)
        }
        r => unreachable!(
            "should not hit this rule {:?}, all our other rules are silent",
            r
        ),
    })
}

/// Read a Verilog memory file from a string containing its contents into a Vec.
///
/// A memory file is composed of items, which are either numeric literals or
/// `@hh..` hex addresses to restart writing at. All instances of `z` and `x` are
/// replaced with zeros. If an address directive `@hh..` points past the end of
/// the memory, the space between where we last wrote and the restart address
/// will be filled with zeros.
///
/// Hex numbers support both upper- and lowercase digits. Both Verilog comment
/// types `/* ... */` and `// ...` are supported, and so are underscore
/// separators in numeric literals.
///
/// Example:
///
/// ```
/// use readmem::{readmem, ContentType};
/// assert_eq!(vec![0, 1, 2], readmem::<u8>("0 1\n2", ContentType::Hex).unwrap());
/// assert_eq!(vec![0, 1, 2], readmem::<u8>("z/* a */x1 1_0", ContentType::Binary).unwrap());
/// ```
pub fn readmem<I>(content: &str, content_type: ContentType) -> Result<Vec<I>, Error>
where
    I: Integral + FromStr + Clone,
{
    let rule = match content_type {
        ContentType::Hex => Rule::readmemh,
        ContentType::Binary => Rule::readmemb,
    };
    let content = ReadmemParser::parse(rule, content)?;

    let mut result = Vec::new();
    let mut pos = 0;
    for val in content {
        if let Rule::EOI = val.as_rule() {
            continue;
        }
        let val = parse_value::<I>(val)?;
        match val {
            Item::Address(a) => pos = a,
            Item::Number(n) => {
                if pos + 1 >= result.len() {
                    result.resize(pos + 1, I::zero());
                }
                result[pos] = n;
                pos += 1;
            }
        }
    }
    Ok(result)
}

#[cfg(doctest)]
mod doctest {
    use doc_comment::doctest;
    doctest!("../README.md");
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_hex() {
        let hex = include_str!("testdata/hex.txt");
        let arr = readmem::<u8>(hex, ContentType::Hex).unwrap();
        let expected = 0..255u8;
        assert_eq!(256, arr.len());
        for (&item, exp) in arr.iter().zip(expected) {
            assert_eq!(item, exp);
        }
    }

    #[test]
    fn test_bin() {
        let bin = include_str!("testdata/bin.txt");
        let arr = readmem::<u16>(bin, ContentType::Binary).unwrap();
        assert_eq!(257, arr.len());
        let expected = 0..256u16;
        for (&item, exp) in arr.iter().zip(expected) {
            assert_eq!(item, exp);
        }
    }

    #[test]
    fn test_addressing() {
        // it's unclear if the Verilog spec allows overwriting previous data but
        // we do
        let testdata = r#"
            f
            @4
            1 2 3
            @4
            4 5 6
            @8
            e
        "#;
        let expected = vec![0xf, 0, 0, 0, 4, 5, 6, 0, 0xe];
        assert_eq!(
            expected,
            readmem::<u32>(testdata, ContentType::Hex).unwrap()
        );
    }
}
