//! # Prefix Parser
//!
//! `prefix_parser` is a library to help you parse bit and byte prefixes;
//! Helping you turn 12MiB into 12582912
//!

#![no_std]
#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::nursery)]
#![deny(clippy::cargo)]

extern crate alloc;

use alloc::{format, string::String, vec::Vec};

static PREFIXES: [char; 11] = ['b', 'k', 'm', 'g', 't', 'p', 'e', 'z', 'y', 'r', 'q'];

/// Parses an array of chars that is known to have a 1 char binary prefix on the end
///
/// # Arguments
///
/// `string_chars`: An array of chars with the last one being a binary prefix and the previous chars being digits
/// `si`: A boolean value specifying whether the chars should be interpreted as binary or SI notation
///
/// # Returns
///
/// An Option<i128> containing the parsed value upon successful parsing.
///
/// If parsing failed, None will be returned
///
/// # Panics
///
/// This function should only panic if the return value was successfully parsed but over or underflowed the i128
///
/// (The value was below -2^127 or above 2^127-1)
///
fn parse_one_letter_prefix(string_chars: &[char], si: bool) -> Option<i128> {
    let prefix = string_chars.last().unwrap();

    let number_length = string_chars.len() - 1;

    if let Some(prefix_value) = PREFIXES
        .iter()
        .position(|&c| c == prefix.to_ascii_lowercase())
    {
        // We have to check that the beginning is actually a number

        // If anyone knows of a more efficient method of doing this, let me know...
        if let Ok(number) = String::from_iter(&string_chars[..number_length]).parse::<i128>() {
            let base: i128 = if si { 1000 } else { 1024 };

            // The prefix value can only be a maximum of 11
            #[allow(clippy::cast_possible_truncation)]
            return Some(number * base.pow(prefix_value as u32));
        }
        // Non-prefix is not a number
        // Fall through to the below error
    }
    // Not a valid prefix
    None
}

/// Parses an array of chars that is known to have a 2 char binary prefix on the end
///
/// # Arguments
///
/// `string_chars`: An array of chars with the last 2 being a binary prefix and the previous chars being digits
///
/// # Returns
///
/// An Option<i128> containing the parsed value upon successful parsing.
///
/// If parsing failed, None will be returned
///
/// # Panics
///
/// This function should only panic if the return value was successfully parsed but over or underflowed the i128
///
/// (The value was below -2^127 or above 2^127-1)
///
fn parse_two_letter_prefix(string_chars: &[char]) -> Option<i128> {
    let number_length = string_chars.len() - 2;

    let prefix = &string_chars[number_length..];

    assert_eq!(prefix.len(), 2);

    let lchar = prefix[1].to_ascii_lowercase();

    // The first thing we check is if the last char is b or i as those are the only supported last chars if it is a two char prefix
    if !['b', 'i'].contains(&lchar) {
        return None;
    }

    // We use SI units if the second char of the prefix is b. EX: mb, kb, tb
    // This has the fun side effect of allowing bb as a prefix
    let si = lchar == 'b';

    // We have number_length + 1 here to strip off the end char and leave the number with a one char prefix.
    // This is fine as all the second char does is determine if the number is SI or binary
    parse_one_letter_prefix(&string_chars[..=number_length], si)
}

/// Parses an array of chars that is known to have a 3 char binary prefix on the end
///
/// # Arguments
///
/// `string_chars`: An array of chars with the last 3 being a binary prefix and the previous chars being digits
///
/// # Returns
///
/// An Option<i128> containing the parsed value upon successful parsing.
///
/// If parsing failed, None will be returned
///
/// # Panics
///
/// This function should only panic if the return value was successfully parsed but over or underflowed the i128
///
/// (The value was below -2^127 or above 2^127-1)
///
fn parse_three_letter_prefix(string_chars: &[char]) -> Option<i128> {
    let number_length = string_chars.len() - 3;

    let prefix = &string_chars[number_length..];

    assert_eq!(prefix.len(), 3);

    // A valid three letter prefix would always be binary, but you know how things are... They're not always valid

    // A valid three letter prefix will ALWAYS have "i" as the middle letter and "b" as the last

    if !prefix[1].eq_ignore_ascii_case(&'i') || !prefix[2].eq_ignore_ascii_case(&'b') {
        return None;
    }

    parse_one_letter_prefix(&string_chars[..=number_length], false)
}

/// Parses a string with a binary prefix on the end and converts it into a number of bytes
///
/// # Arguments
///
/// `prefixed_string`: a &str, such as "5KB" or "2TiB" that should be processed.
///
/// # Returns
///
/// The i128 value of `prefixed_string` interpreted as bytes
///
/// # Panics
///
/// This function will panic if the result adds up to over 2^127-1 bytes or lower than -2^127 bytes.
///
/// (170141183460469231731687303715884105727 and -170141183460469231731687303715884105728 bytes respectively)
///
/// # Errors
///
/// Will return Err if `prefixed_string` is not a valid prefixed string.
///
/// This includes fractional numbers.
///
///
/// # Example:
///
/// ```rust
/// # fn main() -> Result<(), String> {
/// use prefix_parser::parse_prefixes;
///
/// let to_parse = "2KiB";
/// let parsed = parse_prefixes(to_parse)?;
///
/// // 2048 is 2Kib
/// assert_eq!(parsed, 2048);
/// #     Ok(())
/// # }
/// ```
pub fn parse_prefixes(prefixed_string: &str) -> Result<i128, String> {
    if let Ok(parsed) = prefixed_string.parse::<i128>() {
        // If we can parse it without having to worry about a prefix, we should
        return Ok(parsed);
    }

    // We obviously must be working with a prefix or an invalid string

    let string_chars: Vec<char> = prefixed_string.chars().collect();

    let string_length = string_chars.len();
    if string_length < 2 {
        // This isn't possible as we need at least one digit and one letter for the prefix.

        return Err(format!("{prefixed_string} is not a prefixed string"));
    }

    // We need separate special case processing for strings of length 2, and 3. Then a general processing for 4 and up

    // Only one char available for the prefix
    if string_length == 2 {
        if let Some(parsed) = parse_one_letter_prefix(&string_chars, false) {
            return Ok(parsed);
        }
        return Err(format!("{prefixed_string} is not a prefixed string."));
    }

    // Two chars available

    if string_length == 3 {
        // Now the prefix could possibly be the second to last or the last char. Yay
        let prefix = string_chars[1];

        if prefix.is_ascii_digit() {
            // Prefix is only the last char
            if let Some(parsed) = parse_one_letter_prefix(&string_chars, false) {
                return Ok(parsed);
            }
            return Err(format!("{prefixed_string} is not a prefixed string."));
        }

        // Prefix is the second to last char
        if let Some(parsed) = parse_two_letter_prefix(&string_chars) {
            return Ok(parsed);
        }
        return Err(format!("{prefixed_string} is not a prefixed string."));
    }

    // Finally, we can implement the generic parser

    /*
     * Here we check if the 3rd from last char is a digit. If it is, then we cannot have a 3 char
     * prefix so we go on to check the second to last char. if it is also a digit, then there must
     * be a 1 char prefix. If it is not, then it must be a 2 char prefix.
     */
    let prefix = string_chars[string_length - 3];

    if prefix.is_ascii_digit() {
        let prefix = string_chars[string_length - 2];
        if prefix.is_ascii_digit() {
            // 1 char prefix
            if let Some(parsed) = parse_one_letter_prefix(&string_chars, false) {
                return Ok(parsed);
            }
            return Err(format!("{prefixed_string} is not a prefixed string."));
        }
        // 2 char prefix
        if let Some(parsed) = parse_two_letter_prefix(&string_chars) {
            return Ok(parsed);
        }
        return Err(format!("{prefixed_string} is not a prefixed string."));
    }
    // 3 char prefix
    if let Some(parsed) = parse_three_letter_prefix(&string_chars) {
        return Ok(parsed);
    }

    Err(format!("{prefixed_string} is not a prefixed string."))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_one_letter_prefix() {
        let result = parse_prefixes("4k").unwrap();
        assert_eq!(result, 4096);
    }

    #[test]
    fn test_two_letter_binary_prefix() {
        let result = parse_prefixes("4ki").unwrap();
        assert_eq!(result, 4096);
    }

    #[test]
    fn test_two_letter_si_prefix() {
        let result = parse_prefixes("4kb").unwrap();
        assert_eq!(result, 4000);
    }

    #[test]
    fn test_three_letter_prefix() {
        let result = parse_prefixes("4kib").unwrap();
        assert_eq!(result, 4096);
    }

    #[test]
    fn test_long_numbers() {
        let result = parse_prefixes("1000m").unwrap();
        assert_eq!(result, 1048576000);
        let result = parse_prefixes("4212ki").unwrap();
        assert_eq!(result, 4313088);
        let result = parse_prefixes("2231MB").unwrap();
        assert_eq!(result, 2231000000);
        let result = parse_prefixes("12412MiB").unwrap();
        assert_eq!(result, 13014925312);
    }

    #[test]
    fn test_correct_one_letter_prefixes() {
        let result = parse_prefixes("1b").unwrap();
        assert_eq!(result, 1);
        let result = parse_prefixes("1k").unwrap();
        assert_eq!(result, 1024);
        let result = parse_prefixes("1m").unwrap();
        assert_eq!(result, 1048576);
        let result = parse_prefixes("1g").unwrap();
        assert_eq!(result, 1073741824);
        let result = parse_prefixes("1t").unwrap();
        assert_eq!(result, 1099511627776);
        let result = parse_prefixes("1p").unwrap();
        assert_eq!(result, 1125899906842624);
        let result = parse_prefixes("1e").unwrap();
        assert_eq!(result, 1152921504606846976);
        let result = parse_prefixes("1z").unwrap();
        assert_eq!(result, 1180591620717411303424);
        let result = parse_prefixes("1y").unwrap();
        assert_eq!(result, 1208925819614629174706176);
        let result = parse_prefixes("1r").unwrap();
        assert_eq!(result, 1237940039285380274899124224);
        let result = parse_prefixes("1q").unwrap();
        assert_eq!(result, 1267650600228229401496703205376);

        let result = parse_prefixes("1bi").unwrap();
        assert_eq!(result, 1);
        let result = parse_prefixes("1ki").unwrap();
        assert_eq!(result, 1024);
        let result = parse_prefixes("1mi").unwrap();
        assert_eq!(result, 1048576);
        let result = parse_prefixes("1gi").unwrap();
        assert_eq!(result, 1073741824);
        let result = parse_prefixes("1ti").unwrap();
        assert_eq!(result, 1099511627776);
        let result = parse_prefixes("1pi").unwrap();
        assert_eq!(result, 1125899906842624);
        let result = parse_prefixes("1ei").unwrap();
        assert_eq!(result, 1152921504606846976);
        let result = parse_prefixes("1zi").unwrap();
        assert_eq!(result, 1180591620717411303424);
        let result = parse_prefixes("1yi").unwrap();
        assert_eq!(result, 1208925819614629174706176);
        let result = parse_prefixes("1ri").unwrap();
        assert_eq!(result, 1237940039285380274899124224);
        let result = parse_prefixes("1qi").unwrap();
        assert_eq!(result, 1267650600228229401496703205376);

        let result = parse_prefixes("1bib").unwrap();
        assert_eq!(result, 1);
        let result = parse_prefixes("1kib").unwrap();
        assert_eq!(result, 1024);
        let result = parse_prefixes("1mib").unwrap();
        assert_eq!(result, 1048576);
        let result = parse_prefixes("1gib").unwrap();
        assert_eq!(result, 1073741824);
        let result = parse_prefixes("1tib").unwrap();
        assert_eq!(result, 1099511627776);
        let result = parse_prefixes("1pib").unwrap();
        assert_eq!(result, 1125899906842624);
        let result = parse_prefixes("1eib").unwrap();
        assert_eq!(result, 1152921504606846976);
        let result = parse_prefixes("1zib").unwrap();
        assert_eq!(result, 1180591620717411303424);
        let result = parse_prefixes("1yib").unwrap();
        assert_eq!(result, 1208925819614629174706176);
        let result = parse_prefixes("1rib").unwrap();
        assert_eq!(result, 1237940039285380274899124224);
        let result = parse_prefixes("1qib").unwrap();
        assert_eq!(result, 1267650600228229401496703205376);

        let result = parse_prefixes("1bb").unwrap();
        assert_eq!(result, 1);
        let result = parse_prefixes("1kb").unwrap();
        assert_eq!(result, 1000);
        let result = parse_prefixes("1mb").unwrap();
        assert_eq!(result, 1000000);
        let result = parse_prefixes("1gb").unwrap();
        assert_eq!(result, 1000000000);
        let result = parse_prefixes("1tb").unwrap();
        assert_eq!(result, 1000000000000);
        let result = parse_prefixes("1pb").unwrap();
        assert_eq!(result, 1000000000000000);
        let result = parse_prefixes("1eb").unwrap();
        assert_eq!(result, 1000000000000000000);
        let result = parse_prefixes("1zb").unwrap();
        assert_eq!(result, 1000000000000000000000);
        let result = parse_prefixes("1yb").unwrap();
        assert_eq!(result, 1000000000000000000000000);
        let result = parse_prefixes("1rb").unwrap();
        assert_eq!(result, 1000000000000000000000000000);
        let result = parse_prefixes("1qb").unwrap();
        assert_eq!(result, 1000000000000000000000000000000);
    }

    #[test]
    fn test_negatives() {
        let result = parse_prefixes("-1000m").unwrap();
        assert_eq!(result, -1048576000);
        let result = parse_prefixes("-4212ki").unwrap();
        assert_eq!(result, -4313088);
        let result = parse_prefixes("-2231MB").unwrap();
        assert_eq!(result, -2231000000);
        let result = parse_prefixes("-12412MiB").unwrap();
        assert_eq!(result, -13014925312);
    }

    #[test]
    fn test_no_prefix() {
        let result = parse_prefixes("8675309").unwrap();
        assert_eq!(result, 8675309);
    }

    #[test]
    #[should_panic(expected = "attempt to multiply with overflow")]
    fn test_overflow() {
        // This equals 2^127 bytes
        let _result = parse_prefixes("134217728q");
    }

    #[test]
    fn test_below_overflow() {
        let result = parse_prefixes("134217727q").unwrap();

        assert_eq!(result, 170141182192818631503457902219180900352);
        assert_eq!(result, (2u128.pow(127) - 1024u128.pow(10)) as i128);

        let result = parse_prefixes("170141183460469231731687303715884105727BIB").unwrap();

        assert_eq!(result, (2u128.pow(127) - 1) as i128);
        assert_eq!(result, 170141183460469231731687303715884105727);
    }

    #[test]
    fn test_edge_cases() {
        let result = parse_prefixes("1b").unwrap();
        assert_eq!(result, 1);
        let result = parse_prefixes("1bib").unwrap();
        assert_eq!(result, 1);
        let result = parse_prefixes("1bb").unwrap();
        assert_eq!(result, 1);

        let result = parse_prefixes("100000b").unwrap();
        assert_eq!(result, 100000);
        let result = parse_prefixes("100000bib").unwrap();
        assert_eq!(result, 100000);
        let result = parse_prefixes("100000bb").unwrap();
        assert_eq!(result, 100000);
    }

    #[test]
    #[should_panic(expected = "Test Passed")]
    fn test_invalid_one_letter_prefix() {
        let _result = parse_prefixes("1j").expect("Test Passed");
    }

    #[test]
    #[should_panic(expected = "Test Passed")]
    fn test_invalid_input_1() {
        let _result = parse_prefixes("7KBI").expect("Test Passed");
    }

    #[test]
    #[should_panic(expected = "Test Passed")]
    fn test_invalid_input_2() {
        let _result = parse_prefixes("5mn").expect("Test Passed");
    }

    #[test]
    #[should_panic(expected = "Test Passed")]
    fn test_invalid_input_3() {
        let _result = parse_prefixes("1b23434b").expect("Test Passed");
    }

    #[test]
    #[should_panic(expected = "Test Passed")]
    fn test_invalid_input_4() {
        let _result = parse_prefixes("231m4b").expect("Test Passed");
    }
}
