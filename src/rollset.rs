// Copyright (C) 2021 Ben Stern
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use core::convert::Infallible;

use std::error::Error;
use std::fmt::{Display, Debug, Error as FmtError, Formatter};
use std::str::FromStr;

use lazy_static::lazy_static;
use regex::Regex;

use crate::{Dice, DiceParseError};

lazy_static! {
    // ?x ignores space/comments in the regex, not in the string we're checking
    static ref MATH_RE: Regex = Regex::new("(?P<op>[-\u{2212}+xX*\u{00d7}])").expect("Couldn't compile MATH_RE");
}

#[derive(Clone, Debug, PartialEq)]
enum DiceWords {
    Dice(Dice),
    Bonus(u16),
    Plus,
    Minus,
    Times,
    Multiplier(f32),
    Comment(String),
    Other(String),
    Total(i32),
}

impl Display for DiceWords {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FmtError> {
        match self {
            DiceWords::Dice(d) => write!(fmt, "{}", d),
            DiceWords::Bonus(d) => write!(fmt, "{}", d),
            DiceWords::Multiplier(d) => write!(fmt, "{}", d),
            DiceWords::Plus => write!(fmt, "+"),
            DiceWords::Minus => write!(fmt, "\u{2212}"),
            DiceWords::Times => write!(fmt, "\u{00d7}"),
            DiceWords::Other(s) | DiceWords::Comment(s) => write!(fmt, "|{}|", s),
            DiceWords::Total(t) => write!(fmt, "\u{21e8} {}", t),
        }
    }
}

impl FromStr for DiceWords {
    type Err = Infallible;

    fn from_str(line: &str) -> Result<Self, Self::Err> {
        if let Ok(d) = line.parse() {
            Ok(DiceWords::Dice(d))
        } else if let Ok(n) = line.parse() {
            Ok(DiceWords::Bonus(n))
        } else if let Ok(f) = line.parse() {
            Ok(DiceWords::Multiplier(f))
        } else if line == "+" {
            Ok(DiceWords::Plus)
        } else if (line == "-") || (line == "\u{2212}") {
            Ok(DiceWords::Minus)
        } else if (line == "x") || (line == "X") || (line == "*") || (line == "\u{00d7}") {
            Ok(DiceWords::Times)
        } else if line.starts_with('#') {
            Ok(DiceWords::Comment(line.to_string()))
        } else {
            Ok(DiceWords::Other(line.to_string()))
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum RollParseError {
    DiceError(DiceParseError),
    InvalidOrder,
    MissingRoll,
    Failure(String),
}

impl Display for RollParseError {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FmtError> {
        write!(fmt, "{:?}", self)
    }
}

impl Error for RollParseError {}

#[derive(Clone, Debug, PartialEq)]
pub struct RollSet {
    words: Vec<DiceWords>,
}

/// In the syntax below, capital letters are variables and lower-case letters
/// are verbatim.  Optional fields are surrounded with [], mandatory fields are
/// surrounded with <>.
///
/// In use, the parsed syntax is case insensitive and ignores internal spaces.
///
/// Dice may have no more than 1000 sides, not as a technical reason but because
/// the number of times a d1001 or d2000 are needed should be vanishingly low.
///
/// Note that dice math is left to right:
/// - 1 + 2 * 3 = 9, not 7
/// - 1 + 2 * 3 + 4 * 5 = 65, not 27 (nor 29)
/// - There's no way to force precedence except for ordering
/// - This is a feature; 2d6 + 4 * 2 + 1d6 is a common pattern
///
/// Line syntax: `<M | X | R | C> [M | X | R | C]...`
///
/// Example: `lance 2d6 + 4 * 2 slashing + 1d6 fire`
///
/// - M: a modifier, defined below
/// - X: a multiplier, defined below
/// - R: a roll, defined below
/// - C: a comment (anything that doesn't match one of the above)
///
/// Bonus syntax: `<+ | -> N`
///
/// Examples: `-5` or `+ 4`
///
/// - the sign is required
/// - N is the value, and must be an integer
/// - "+1.5" will be interpreted as +1 ".5"
///
/// Multiplier syntax: `<x | *> F`
///
/// Examples: `x 1.5` or `*2`
///
/// - x, X, and * are accepted
/// - \x00d7 and \x2a09 aren't accepted and will cause this to be parsed as a
///   comment
/// - F is either an integer or a floating point number
/// - results are rounded down
///
/// Examples (sample use case in parens)
/// - `3d8` (roll 3d8)
/// - `d20lh19!` (roll a keen d20 which explodes, coloring 19s & 20s but not 1s)
///   (not implemented)
/// - `2d20/l` (disadvantage, roll 2d20 but only keep the lower one)
/// - `4d6/h3` (use a typical method to generate a stat)
///
/// Longer examples with surrounding modifiers and comments:
/// - `3d8` bludgeoning (a damage roll)
/// - `d20l2h2+8 to hit` (threat on 19-20, fail on 1-2)
/// - `2d20/l+4 fort save with disadvantage`
/// - `4d6/h3 4d6/h3 4d6/h3 4d6/h3 4d6/h3 4d6/h3 chargen` (the reader should
///   ignore the total shown; external syntax should be created to roll without
///   totalling)
///
/// - The leading plus is optional
///   - implemented
///   - It's normally used to join 2 rolls, but it isn't required
///   - Negative rolls aren't parsed as such (the "-" is considered a comment)
/// - N: the number of dice to roll
///   - implemented
///   - If missing, 1 is assumed
///   - An explicit 0 is an error (to avoid interpreting 0d6 as "0" 1d6)
/// - M: the number of sides
///   - implemented
///   - 0 is an error
///   - 1 is legal but largely useless
///   - f (or F) means Fate dice
///   - If this is missing then the roll can't be parsed as such and will be
///     interpreted as a comment
/// - X: the number of dice to keep
///   - not implemented
///   - /hX will mean keep the highest X rolls
///   - /lX will mean keep the lowest X rolls
///   - incompatible with `!` (bang)
///   - X > N is an error
///   - X = N is ignored entirely
///   - X = 0 is an error
///   - must come after H and L if they're present
/// - ! means exploding
///   - implemented for highest number only
///   - must be the last thing on the dice roll
///   - E means explode on E or higher, not just the highest number
///   - E <= 1 is an error
///   - E > N is ignored (but not an error)
///   - Fate dice and one-sided dice can't explode
///   - exploded dice don't count against the limit per roll (explosions don't
///     usually last long anyway)

impl FromStr for RollSet {
    type Err = RollParseError;

    fn from_str(line: &str) -> Result<Self, Self::Err> {
        let mut last_word = DiceWords::Other("".to_string());
        let mut words = Vec::new();
        let mut roll_found = false;
        let mut total = 0;
        let replaced = MATH_RE.replace_all(line, " $op ");
        let mut each = replaced.split_whitespace();
        while let Some(word) = each.next() {
            let parsed = word.parse::<DiceWords>().unwrap();
            //println!("{}", word);
            match (&last_word, &parsed) {
                (DiceWords::Dice(_), DiceWords::Dice(_)) | // 3d4 3d4
                (DiceWords::Dice(_), DiceWords::Multiplier(_)) | // 3d6 4.4
                (DiceWords::Dice(_), DiceWords::Bonus(_)) | // 4d6 4

                (DiceWords::Bonus(_), DiceWords::Dice(_)) | // 4 4d6
                (DiceWords::Bonus(_), DiceWords::Bonus(_)) | // 4 4
                (DiceWords::Bonus(_), DiceWords::Multiplier(_)) | // 4 4.4

                (DiceWords::Times, DiceWords::Dice(_)) | // * 4d6

                (DiceWords::Plus, DiceWords::Plus) | // + +
                (DiceWords::Plus, DiceWords::Minus) | // + -
                (DiceWords::Plus, DiceWords::Times) | // + *
                (DiceWords::Plus, DiceWords::Multiplier(_)) | // + 4.4
                (DiceWords::Plus, DiceWords::Comment(_)) | // + # foo
                (DiceWords::Plus, DiceWords::Other(_)) | // + foo // should this be allowed?

                (DiceWords::Minus, DiceWords::Plus) | // - +
                (DiceWords::Minus, DiceWords::Minus) | // - -
                (DiceWords::Minus, DiceWords::Times) | // - *
                (DiceWords::Minus, DiceWords::Multiplier(_)) | // - 4.4
                (DiceWords::Minus, DiceWords::Comment(_)) | // - # foo
                (DiceWords::Minus, DiceWords::Other(_)) | // - foo // should this be allowed?

                (DiceWords::Times, DiceWords::Plus) | // * +
                (DiceWords::Times, DiceWords::Minus) | // * - (this means * -4 doesn't work)
                (DiceWords::Times, DiceWords::Times) | // * *
                (DiceWords::Times, DiceWords::Comment(_)) | // * # foo
                (DiceWords::Times, DiceWords::Other(_)) | // * foo

                (DiceWords::Multiplier(_), DiceWords::Dice(_)) | // 4.4 4d6
                (DiceWords::Multiplier(_), DiceWords::Bonus(_)) | // 4.4 4
                (DiceWords::Multiplier(_), DiceWords::Multiplier(_)) | // 4.4 4.4
                (DiceWords::Multiplier(_), DiceWords::Other(_)) | // * fire
                (DiceWords::Multiplier(_), DiceWords::Comment(_)) | // * # foo

                (DiceWords::Other(_), DiceWords::Bonus(_)) | // fire 4
                (DiceWords::Other(_), DiceWords::Multiplier(_))

                => { // fire 4.4
                    return Err(RollParseError::InvalidOrder);
                },

                (DiceWords::Dice(_), DiceWords::Plus) | // 4d6 +
                (DiceWords::Dice(_), DiceWords::Minus) | // 4d6 -
                (DiceWords::Dice(_), DiceWords::Times) | // 4d6 *
                (DiceWords::Dice(_), DiceWords::Other(_)) | // 4d6 fire

                (DiceWords::Bonus(_), DiceWords::Plus) | // 4 +
                (DiceWords::Bonus(_), DiceWords::Minus) | // 4 -
                (DiceWords::Bonus(_), DiceWords::Times) | // 4 *
                (DiceWords::Bonus(_), DiceWords::Other(_)) | // 4 fire

                (DiceWords::Multiplier(_), DiceWords::Plus) | // 4.4 +
                (DiceWords::Multiplier(_), DiceWords::Minus) | // 4.4 -
                (DiceWords::Multiplier(_), DiceWords::Times) | // 4.4 *

                (DiceWords::Other(_), DiceWords::Plus) | // fire +
                (DiceWords::Other(_), DiceWords::Minus) | // fire -
                (DiceWords::Other(_), DiceWords::Times) // fire *
                => {
                    words.push(parsed.clone());
                    last_word = parsed;
                },

                (DiceWords::Plus, DiceWords::Bonus(b)) => { // + 4
                    total += *b as i32;
                    words.push(parsed.clone());
                    last_word = parsed;
                },

                (DiceWords::Minus, DiceWords::Bonus(b)) => { // + 4
                    total -= *b as i32;
                    words.push(parsed.clone());
                    last_word = parsed;
                },

                (DiceWords::Times, DiceWords::Bonus(b)) => {
                    total *= *b as i32;
                    last_word = DiceWords::Multiplier(*b as f32);
                    words.push(last_word.clone());
                }

                (DiceWords::Times, DiceWords::Multiplier(b)) => {
                    total = (total as f32 * b) as i32;
                    words.push(parsed.clone());
                    last_word = parsed;
                }

                (DiceWords::Dice(_), DiceWords::Comment(s)) | // 4d6 # first
                (DiceWords::Bonus(_), DiceWords::Comment(s)) | // 4 # foo
                (DiceWords::Other(_), DiceWords::Comment(s)) // fire # foo
                => {
                    //println!("Pushing in total");
                    words.push(DiceWords::Total(total));
                    last_word = DiceWords::Comment(each.fold(s.to_string(), |acc, x| acc + " " + x));
                    //println!("now adding comment: {:?}", last_word);
                    words.push(last_word.clone());
                    break;
                },

                (DiceWords::Other(_), DiceWords::Dice(d)) | // 1st attack 4d6 (also initial condition)
                (DiceWords::Plus, DiceWords::Dice(d)) | // + 4d6
                (DiceWords::Minus, DiceWords::Dice(d)) => { // - 4d6
                    last_word = parsed.clone();
                    words.push(parsed.clone());
                    roll_found = true;
                    total += d.total();
                },

                (_, DiceWords::Total(_)) |
                (DiceWords::Total(_), _) |
                (DiceWords::Comment(_), _) => {
                    // should be impossible, last_word is never set to Comment or Total
                    return Err(RollParseError::Failure(line.to_string()));
                },

                (DiceWords::Other(t), DiceWords::Other(s)) => { // foo bar
                    words.pop();
                    last_word = DiceWords::Other(format!("{} {}", t, s));
                    words.push(last_word.clone());
                },
            }
        }
        if !roll_found {
            Err(RollParseError::MissingRoll)
        } else {
            //println!("last_word: {:?}", last_word);
            if !matches!(last_word, DiceWords::Comment(_)) {
                //println!("pushing in total due to lack of comment");
                words.push(DiceWords::Total(total));
            }
            Ok(RollSet { words })
        }
    }
}

impl Display for RollSet {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FmtError> {
        write!(fmt, "{}", self.words.iter().map(|w| format!("{}", w)).collect::<Vec<String>>().join(" "))
    }
}

#[cfg(test)]
mod test {
    use super::{Dice, DiceWords, RollParseError, RollSet};
    use crate::expect_dice_similar;

    macro_rules! expect_rollset_similar {
        ($text: literal, $expect: expr) => {
            for (r, w) in $text.parse::<RollSet>().unwrap().words.iter().zip($expect) {
                match (r, w) {
                    (DiceWords::Dice(parsed), DiceWords::Dice(provided)) => {
                        expect_dice_similar!(parsed, provided);
                    },
                    (DiceWords::Bonus(parsed), DiceWords::Bonus(provided)) => assert_eq!(parsed, provided),
                    (DiceWords::Multiplier(parsed), DiceWords::Multiplier(provided))  => assert_eq!(parsed, provided),
                    (DiceWords::Comment(parsed), DiceWords::Comment(provided)) => assert_eq!(parsed, provided),
                    (x, y) => assert_eq!(x, y),
                }
            }
        }
    }

    #[test]
    fn four() {
        assert_eq!("4".parse::<RollSet>(), Err(RollParseError::InvalidOrder));
        assert_eq!("4+1d4".parse::<RollSet>(), Err(RollParseError::InvalidOrder));
    }

    #[test]
    fn exploding_1d20plus4() {
        expect_rollset_similar!("1d20+4", &[ DiceWords::Dice(Dice::new(1, 20).unwrap()), DiceWords::Plus, DiceWords::Bonus(4) ]);
    }

    #[test]
    fn r_1d6plus3() {
        expect_rollset_similar!("1d6+3", &[ DiceWords::Dice(Dice::new(1, 6).unwrap()), DiceWords::Plus, DiceWords::Bonus(3) ]);
    }

    #[test]
    fn caps_1d20plus4() {
        expect_rollset_similar!("1D20+4", &[ DiceWords::Dice(Dice::new(1, 20).unwrap()), DiceWords::Plus, DiceWords::Bonus(4) ]);
    }

    #[test]
    fn caps_1d20minus4() {
        expect_rollset_similar!("1D20 - 4", &[ DiceWords::Dice(Dice::new(1, 20).unwrap()), DiceWords::Minus, DiceWords::Bonus(4) ]);
    }

    #[test]
    fn comment_1d20() {
        expect_rollset_similar!("1d20 for a test", &[
            DiceWords::Dice(Dice::new(1, 20).unwrap()),
            DiceWords::Other("for a test".to_string()),
        ]);
    }

    #[test]
    fn t_mult() {
        expect_rollset_similar!("1d20 * 1.5", &[
            DiceWords::Dice(Dice::new(1, 20).unwrap()),
            DiceWords::Times,
            DiceWords::Multiplier(1.5),
        ]);
    }

    #[test]
    fn spacesplus() {
        expect_rollset_similar!("1d6+4+11d99!+3dF+ 4 +3 + 2 + 1d5", &[
            DiceWords::Dice(Dice::new(1, 6).unwrap()),
            DiceWords::Plus,
            DiceWords::Bonus(4),
            DiceWords::Plus,
            DiceWords::Dice(Dice::new_extended(11, 99, 0, 99).unwrap()),
            DiceWords::Plus,
            DiceWords::Dice(Dice::new(3, 0).unwrap()),
            DiceWords::Plus,
            DiceWords::Bonus(4),
            DiceWords::Plus,
            DiceWords::Bonus(3),
            DiceWords::Plus,
            DiceWords::Bonus(2),
            DiceWords::Plus,
            DiceWords::Dice(Dice::new(1, 5).unwrap()),
        ]);
    }

    #[test]
    fn spacesminus() {
        expect_rollset_similar!("1d6-4+11d99-3dF+ 4 +3 - 2 - 1d5", &[
            DiceWords::Dice(Dice::new(1, 6).unwrap()),
            DiceWords::Minus,
            DiceWords::Bonus(4),
            DiceWords::Plus,
            DiceWords::Dice(Dice::new(11, 99).unwrap()),
            DiceWords::Minus,
            DiceWords::Dice(Dice::new(3, 0).unwrap()),
            DiceWords::Plus,
            DiceWords::Bonus(4),
            DiceWords::Plus,
            DiceWords::Bonus(3),
            DiceWords::Minus,
            DiceWords::Bonus(2),
            DiceWords::Minus,
            DiceWords::Dice(Dice::new(1, 5).unwrap()),
        ]);
    }

#[cfg(test)]
    macro_rules! unwrap_dice {
        ($d: expr) => {
            if let DiceWords::Dice(roll) = $d {
                roll
            } else {
                panic!("not a roll: {:?}", $d);
            }
        }
    }

    #[test]
    fn coinflip() {
        let rs = "1d2 # 1 = foo, 2=bar".parse::<RollSet>().unwrap();
        expect_dice_similar!(unwrap_dice!(&rs.words[0]), Dice::new(1, 2).unwrap());
        assert_eq!(rs.words[2], DiceWords::Comment("# 1 = foo, 2=bar".to_string()));
    }

    // older tests

    #[test]
    fn compact() {
        let rs = "2d6+4 for a test".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 5);

        let mut iter = rs.words.iter();

        let roll = unwrap_dice!(iter.next().unwrap());
        assert_eq!(roll.rolls().len(), 2);
        assert_eq!(roll.sides(), 6);

        assert_eq!(iter.next().unwrap(), &DiceWords::Plus);
        assert_eq!(iter.next().unwrap(), &DiceWords::Bonus(4));
        assert_eq!(iter.next().unwrap(), &DiceWords::Other("for a test".to_string()));
        assert!(matches!(iter.next().unwrap(), &DiceWords::Total(_)));
    }

    #[test]
    fn whitespace_positive() {
        let rs = "2d6 + 4 for a test".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 5);

        let mut iter = rs.words.iter();

        let roll = unwrap_dice!(iter.next().unwrap());
        assert_eq!(roll.rolls().len(), 2);
        assert_eq!(roll.sides(), 6);

        assert_eq!(iter.next().unwrap(), &DiceWords::Plus);
        assert_eq!(iter.next().unwrap(), &DiceWords::Bonus(4));
        assert_eq!(iter.next().unwrap(), &DiceWords::Other("for a test".to_string()));
        assert!(matches!(iter.next().unwrap(), DiceWords::Total(_)));
    }

    #[test]
    fn whitespace_negative() {
        let rs = "2d6 - 4 for a test".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 5);

        let mut iter = rs.words.iter();

        let roll = unwrap_dice!(iter.next().unwrap());
        assert_eq!(roll.rolls().len(), 2);
        assert_eq!(roll.sides(), 6);

        assert_eq!(iter.next().unwrap(), &DiceWords::Minus);
        assert_eq!(iter.next().unwrap(), &DiceWords::Bonus(4));
        assert_eq!(iter.next().unwrap(), &DiceWords::Other("for a test".to_string()));
        assert!(matches!(iter.next().unwrap(), DiceWords::Total(_)));
    }

    #[test]
    fn simple() {
        let rs = "d20".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 2);

        let roll = unwrap_dice!(&rs.words[0]);
        assert_eq!(roll.rolls().len(), 1);
        assert_eq!(roll.sides(), 20);

        assert!(matches!(rs.words[1], DiceWords::Total(_)));
    }

    #[test]
    fn no_bonus_suffix() {
        let rs = "3d6 Int".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 3);

        let roll = unwrap_dice!(&rs.words[0]);
        assert_eq!(roll.rolls().len(), 3);
        assert_eq!(roll.sides(), 6);

        assert_eq!(rs.words[1], DiceWords::Other("Int".to_string()));
        assert!(matches!(rs.words[2], DiceWords::Total(_)));
    }

    #[test]
    fn only_bonus() {
        let rs = "d8+2".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 4);

        let roll = unwrap_dice!(&rs.words[0]);
        assert_eq!(roll.rolls().len(), 1);
        assert_eq!(roll.sides(), 8);

        assert_eq!(rs.words[1], DiceWords::Plus);
        assert_eq!(rs.words[2], DiceWords::Bonus(2));
        assert!(matches!(rs.words[3], DiceWords::Total(_)));
    }

    #[test]
    fn test_only_penalty() {
        let rs = "3d8-2".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 4);

        let roll = unwrap_dice!(&rs.words[0]);
        assert_eq!(roll.rolls().len(), 3);
        assert_eq!(roll.sides(), 8);

        assert_eq!(rs.words[1], DiceWords::Minus);
        assert_eq!(rs.words[2], DiceWords::Bonus(2));
    }

    #[test]
    fn bonus_and_roll() {
        let rs = "d8+2 slashing".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 5);

        let roll = unwrap_dice!(&rs.words[0]);
        assert_eq!(roll.sides(), 8);
        assert_eq!(roll.rolls().len(), 1);

        assert_eq!(rs.words[1], DiceWords::Plus);
        assert_eq!(rs.words[2], DiceWords::Bonus(2));
        assert_eq!(rs.words[3], DiceWords::Other("slashing".to_string()));
    }

    #[test]
    fn two_dice_sizes() {
        let rs = "2d5 + 3d9".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 4);
        let mut iter = rs.words.iter();

        let d = unwrap_dice!(iter.next().unwrap());
        assert_eq!(d.rolls().len(), 2);
        assert_eq!(d.sides(), 5);

        assert_eq!(iter.next().unwrap(), &DiceWords::Plus);

        let d = unwrap_dice!(iter.next().unwrap());
        assert_eq!(d.rolls().len(), 3);
        assert_eq!(d.sides(), 9);
    }

    #[test]
    fn two_rolls_text() {
        let rs = "2d5 + 3d9 for foo, 4d6 for bar".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 7);
        let mut iter = rs.words.iter();

        let d = unwrap_dice!(iter.next().unwrap());
        assert_eq!(d.rolls().len(), 2);
        assert_eq!(d.sides(), 5);

        assert_eq!(iter.next().unwrap(), &DiceWords::Plus);

        let d = unwrap_dice!(iter.next().unwrap());
        assert_eq!(d.rolls().len(), 3);
        assert_eq!(d.sides(), 9);

        assert_eq!(iter.next().unwrap(), &DiceWords::Other("for foo,".to_string()));

        let d = unwrap_dice!(iter.next().unwrap());
        assert_eq!(d.rolls().len(), 4);
        assert_eq!(d.sides(), 6);

        assert_eq!(iter.next().unwrap(), &DiceWords::Other("for bar".to_string()));
    }

    #[test]
    fn roll_no_d0() {
        let rsr = "3d0".parse::<RollSet>();
        assert_eq!(rsr, Err(RollParseError::MissingRoll));

        let rsr = "0d5".parse::<RollSet>();
        assert_eq!(rsr, Err(RollParseError::MissingRoll));
    }

    #[test]
    fn roll_d1() {
        let rs = "3d1".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 2);

        let roll = unwrap_dice!(&rs.words[0]);
        assert_eq!(roll.sides(), 1);
        assert_eq!(roll.total(), 3);
        assert_eq!(rs.words[1], DiceWords::Total(3));
    }

    // Using the dice roller as a calculator is no longer allowed.

    #[test]
    fn roll_no_dice() {
        let rsr = "4".parse::<RollSet>();
        assert_eq!(rsr, Err(RollParseError::InvalidOrder));
    }

    #[test]
    fn roll_no_dice_plus() {
        let rsr = "+4".parse::<RollSet>();
        assert_eq!(rsr, Err(RollParseError::MissingRoll));
    }

    #[test]
    fn roll_simple_math() {
        let rsr = "2 +4-1".parse::<RollSet>();
        assert_eq!(rsr, Err(RollParseError::InvalidOrder));
    }

    #[test]
    fn roll_bad_dice() {
        assert_eq!("4d-4".parse::<RollSet>(), Err(RollParseError::MissingRoll));
        assert_eq!("ddd".parse::<RollSet>(), Err(RollParseError::MissingRoll));
    }

    #[test]
    fn leading_space() {
        let rs = " 4d20 * 1.5".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 4);

        let d = unwrap_dice!(&rs.words[0]);
        assert_eq!(d.sides(), 20);
        assert_eq!(d.rolls().len(), 4);

        assert_eq!(rs.words[1], DiceWords::Times);
        assert_eq!(rs.words[2], DiceWords::Multiplier(1.5));
        assert!(matches!(rs.words[3], DiceWords::Total(_)));
    }

    #[test]
    fn leading_tab() {
        let rs = "\u{0009}4d20*1.5".parse::<RollSet>().unwrap();
        //println!("{:?}", rs.words);
        assert_eq!(rs.words.len(), 4);

        let d = unwrap_dice!(&rs.words[0]);
        assert_eq!(d.sides(), 20);
        assert_eq!(d.rolls().len(), 4);

        assert_eq!(rs.words[1], DiceWords::Times);
        assert_eq!(rs.words[2], DiceWords::Multiplier(1.5));
        assert!(matches!(rs.words[3], DiceWords::Total(_)));
    }

    #[test]
    fn add_constant() {
        let rs = "1d1+4".parse::<RollSet>().unwrap();
        //println!("{:?}", rs.words);
        assert_eq!(rs.words.len(), 4);

        let roll = unwrap_dice!(&rs.words[0]);
        assert_eq!(roll.sides(), 1);
        assert_eq!(roll.total(), 1);
        assert_eq!(rs.words[1..], [ DiceWords::Plus, DiceWords::Bonus(4), DiceWords::Total(5) ]);
    }

    #[test]
    fn add_to_many() {
        let rs = "d20 + d6 + 4 to hit".parse::<RollSet>().unwrap();
        assert_eq!(rs.words.len(), 7);

        let mut iter = rs.words.iter();

        let d = unwrap_dice!(iter.next().unwrap());
        assert_eq!(d.sides(), 20);
        assert_eq!(d.rolls().len(), 1);

        assert_eq!(iter.next().unwrap(), &DiceWords::Plus);

        let d = unwrap_dice!(iter.next().unwrap());
        assert_eq!(d.sides(), 6);
        assert_eq!(d.rolls().len(), 1);

        assert_eq!(iter.next().unwrap(), &DiceWords::Plus);
        assert_eq!(iter.next().unwrap(), &DiceWords::Bonus(4));
        assert_eq!(iter.next().unwrap(), &DiceWords::Other("to hit".to_string()));
    }

    #[test]
    fn add_constant_str() {
        let rsr = "d1+4".parse::<RollSet>();
        assert!(rsr.is_ok());

        let rs = rsr.unwrap();
        assert_eq!("1d1 [1] + 4 \u{21e8} 5".to_string(), format!("{}", rs));
    }

    #[test]
    fn many_rollv_str() {
        let rs = "d1 + 2d1 - 4 to hit".parse::<RollSet>().unwrap();
        assert_eq!("1d1 [1] + 2d1 [2] \u{2212} 4 |to hit| \u{21e8} -1", format!("{}", rs));
    }

    #[test]
    fn multiply_even() {
        let rs = "10d1*1.5".parse::<RollSet>().unwrap();
        assert_eq!("10d1 [10] \u{00d7} 1.5 \u{21e8} 15", format!("{}", rs));
    }

    #[test]
    fn multiply_odd() {
        let rs = "11d1*1.5".parse::<RollSet>().unwrap();
        assert_eq!("11d1 [11] \u{00d7} 1.5 \u{21e8} 16", format!("{}", rs));
    }

    #[test]
    fn multiply_ooo() {
        let rs = "1d1*1.5 + 1d1 * 1.5".parse::<RollSet>().unwrap();
        assert_eq!("1d1 [1] \u{00d7} 1.5 + 1d1 [1] \u{00d7} 1.5 \u{21e8} 3", format!("{}", rs));
        // vs (1 * 1.5 = 1) + (1 * 1.5 = 1) = 2
    }

    #[test]
    fn more_like_chat() {
        let line = "/roll d1 + 2d1 - 4 to hit; 1d1 for damage";
        let chatter: Vec<&str> = line.splitn(2, char::is_whitespace).collect();
        assert_eq!(chatter.len(), 2);
        assert!(chatter[0].starts_with("/r"));

        let rolls: Result<String, RollParseError> = chatter[1].split(';').try_fold("".to_string(), |acc, x| {
            let rs = x.parse::<RollSet>()?;
            if acc.is_empty() {
                Ok(format!("rolls {}", rs))
            } else {
                Ok(acc + &format!("; {}", rs))
            }
        });

        assert!(rolls.is_ok());
        assert_eq!(rolls.unwrap(), "rolls 1d1 [1] + 2d1 [2] \u{2212} 4 |to hit| \u{21e8} -1; 1d1 [1] |for damage| \u{21e8} 1");
    }

    #[test]
    fn dice_from_str() {
        assert_eq!(Ok(Dice::new(1, 1).unwrap()), "1d1".parse());
    }

    #[test]
    fn big_dice_bad() {
        assert_eq!("d10000".parse::<RollSet>(), Err(RollParseError::MissingRoll));
        assert_eq!("1d10000".parse::<RollSet>(), Err(RollParseError::MissingRoll));
        assert_eq!("10001d10".parse::<RollSet>(), Err(RollParseError::MissingRoll));
    }

    #[test]
    fn comment() {
        assert_eq!(format!("{}", "4d1 # foo".parse::<RollSet>().unwrap()), "4d1 [4] \u{21e8} 4 |# foo|");
    }

//#[test]
//    fn multi_roll() {
//        assert_eq!(join_rolls("4d1; 2d1"), "rolls 4d1 [4] \u{21e8} 4; 2d1 [2] = 2");
//    }

//#[test]
//    fn multi_roll_comment() {
//        assert_eq!(join_rolls("4d1 # foo; 2d1"), "rolls 4d1 [4] \u{21e8} 4 # foo; 2d1 [2] \u{21e8} 2");
//    }
}
