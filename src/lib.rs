#![no_std]

#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::nursery)]
#![deny(clippy::cargo)]

extern crate alloc;

use alloc::{format, vec::Vec, string::String};

static PREFIXES: [char; 11] = ['b', 'k', 'm', 'g', 't', 'p', 'e', 'z', 'y', 'r', 'q'];

/// Parses a string where the prefix is the last char
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


/// # Errors
///
/// Will return Err if `prefixed_string` is not a valid prefixed string
pub fn parse_prefixes(prefixed_string: &str) -> Result<i128, String> {
    if let Ok(parsed) = prefixed_string.parse::<i128>() {
        // If we can parse it without having to worry about and prefix, we should
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

    /* Here we check if the 3rd from last char is a digit. If it is, then we cannot have a 3 char
      prefix so we go on to check the second to last char. if it is also a digit, then there must
      be a 1 char prefix. If it is not, then it must be a 2 char prefix.
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
    #[should_panic]
    fn test_invalid_one_letter_prefix() {
        let _result = parse_prefixes("1j").expect("Test Passed");
    }

    #[test]
    #[should_panic]
    fn test_invalid_input_1() {
        let _result = parse_prefixes("7KBI").expect("Test Passed");
    }

    #[test]
    #[should_panic]
    fn test_invalid_input_2() {
        let _result = parse_prefixes("5mn").expect("Test Passed");
    }

    #[test]
    #[should_panic]
    fn test_invalid_input_3() {
        let _result = parse_prefixes("1b23434b").expect("Test Passed");
    }

    #[test]
    #[should_panic]
    fn test_invalid_input_4() {
        let _result = parse_prefixes("231m4b").expect("Test Passed");
    }
}
