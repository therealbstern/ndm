// Copyright (C) 2021 Ben Stern
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

use std::cmp::Ordering;
use std::convert::TryFrom;
use std::error::Error;
use std::fmt::{Display, Debug, Error as FmtError, Formatter};
use std::str::FromStr;

use lazy_static::lazy_static;
use rand::{thread_rng, Rng};
use regex::{Captures, Regex};

lazy_static! {
    // ?x ignores space/comments in the regex, not in the string we're checking
    static ref DICE_RE: Regex = Regex::new(r"(?xi)                 # ignore case
        ^
        (?P<count> [1-9]\d*)?d(?P<sides> f|(?: [1-9]\d*))   # NdM/dM/NdF/dF
        (?:/ (?P<updown> [HL]) (?P<amount> [1-9]\d*))?
        (?P<exploding> ! (?P<fuse> [0-9]+)?)?
        $
        ").expect("Couldn't compile DICE_RE");
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum DiceParseError {
    /// A fuse of 1 was provided; such a fuse would always explode.
    ShortFuse,
    /// More dice were kept than rolled.
    TooManyKept(isize),
    /// Fate dice and d1s can't explode.
    CannotExplode,
    /// Dice were requested with more sides than [Dice::SIDES_LIMIT].
    TooManySides(u16),
    /// A request for dice with no sides.
    ZeroSides,
    /// More than [Dice::COUNT_LIMIT] were requested.
    TooManyDice(usize),
    /// Not in the correct format (\[`n`\]d\[`m`]\[/<H|L>`keep`\]\[!\[`fuse`\]\]).
    Unparseable,
    /// The dice-matching regular expression matched when it shouldn't have,
    /// which is probably a bug in `ndm`.
    Regex
}

impl Eq for DiceParseError {}

impl Display for DiceParseError {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FmtError> {
        write!(fmt, "{:?}", self)
    }
}

impl Error for DiceParseError {}

#[derive(Clone, Debug, PartialEq)]
pub struct Dice {
    count: usize,
    sides: u16,
    keep: isize,
    fuse: u16,
    rolls: Vec<u16>,
    total: i32,
}

impl Dice {
    /// There's no compelling reason to roll more than 100 dice at a time.  I
    /// can't really see why anyone would want to roll more than about 20 at a
    /// time, but 100d6 is a sort of obvious thing for people to do.
    pub const COUNT_LIMIT: usize = 100;

    /// There's no good reason to want anything bigger than a d1000.  Even that
    /// is pushing it, but I can think of games that wanted d1000s for no good
    /// reason.
    pub const SIDES_LIMIT: u16 = 1000;

    pub fn new(n: usize, m: u16) -> Result<Self, DiceParseError> {
        Dice::new_extended(n, m, 0, 0)
    }

    pub fn new_exploding(count: usize, sides: u16, fuse: u16) -> Result<Self, DiceParseError> {
        Dice::new_extended(count, sides, 0, fuse)
    }

    pub fn new_keep_n(count: usize, sides: u16, n: isize) -> Result<Self, DiceParseError> {
        Dice::new_extended(count, sides, n, 0)
    }

    pub fn new_extended(count: usize, sides: u16, keep: isize, fuse: u16) -> Result<Self, DiceParseError> {
        //println!("Called with count: {}, sides: {}, keep: {}, fuse: {}", count, sides, keep, fuse);
        if sides > Self::SIDES_LIMIT {
            return Err(DiceParseError::TooManySides(sides));
        } else if sides < 2 {
            if keep != 0 {
                return Err(DiceParseError::TooManyKept(keep));
            }
            if fuse != 0 {
                return Err(DiceParseError::CannotExplode);
            }
        }
        if count > Self::COUNT_LIMIT {
            return Err(DiceParseError::TooManyDice(count));
        }
        if fuse == 1 {
            return Err(DiceParseError::ShortFuse);
        }

        let mut rolls;
        let mut rng = thread_rng();

        let total = match sides {
            0 => {
                rolls = vec![0; 3];
                for _ in 0 .. count {
                    let last_roll = rng.gen_range(0 ..= 2);
                    rolls[last_roll as usize] += 1;
                }
                (rolls[2] as i32) - (rolls[0] as i32)
            },
            1 => {
                rolls = Vec::with_capacity(0);
                count as i32
            },
            _ => {
                rolls = Vec::new();
                for _ in 0 .. count {
                    let mut last_roll = rng.gen_range(1 ..= sides);
                    rolls.push(last_roll);
                    if fuse > 1 {
                        while last_roll >= fuse {
                            last_roll = rng.gen_range(1 ..= sides);
                            rolls.push(last_roll);
                        }
                    }
                }
                if keep != 0 {
                    rolls.sort_unstable();
                }
                let range = match keep.cmp(&0) {
                    Ordering::Less => {
                        if rolls.len() < (-keep) as usize {
                            return Err(DiceParseError::TooManyKept(keep));
                        }
                        0 .. (-keep as usize)
                    },
                    Ordering::Greater => {
                        if rolls.len() < keep as usize {
                            return Err(DiceParseError::TooManyKept(keep));
                        }
                        rolls.len() - (keep as usize) .. rolls.len()
                    },
                    Ordering::Equal => 0 .. rolls.len(),
                };

                rolls[range].iter().map(|&x| x as i32).sum()
            }
        };
        Ok(Dice { count, sides, fuse, rolls, keep, total })
    }

    pub fn total(&self) -> i32 { self.total }
    pub fn sides(&self) -> u16 { self.sides }
    pub fn count(&self) -> usize { self.count }
    pub fn rolls(&self) -> &Vec<u16> { &self.rolls }
    pub fn fuse(&self) -> u16 { self.fuse }
}

impl Display for Dice {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FmtError> {
        match self.sides {
            // Fate dice can't explode; they don't at construction, but we
            // shouldn't imply they can.
            0 => write!(fmt, "{}dF", self.count)?,
            // neither can a d1 (which is mostly implemented for testing)
            1 => write!(fmt, "{}d1", self.count)?,
            x => {
                write!(fmt, "{}d{}", self.count, x)?;
                if self.fuse > 1 {
                    write!(fmt, "!")?;
                    if self.fuse != self.sides {
                        write!(fmt, "{}", x)?;
                    }
                }
            }
        }

        let count = self.rolls.len();
        if self.sides == 0 {
            if count > 1 {
                write!(fmt, " ([-\u{00d7}{}, _\u{00d7}{}, +\u{00d7}{}] \u{21e8} {:+})",
                self.rolls[0], self.rolls[1], self.rolls[2], self.total)
            } else {
                write!(fmt, " [{:+}]", self.total)
            }
        } else if self.sides == 1 {
            write!(fmt, " [{}]", self.total)
        } else {
            // TODO if there are a jillion rolls, only print summaries (a la the Fate dice above)
            if self.rolls.len() > 1 {
                write!(fmt, " ({:?} \u{21e8} {})", self.rolls, self.total)
            } else {
                write!(fmt, " [{}]", self.total)
            }
        }
    }
}

impl Dice {
    pub const SIDE_LIMIT: u16 = 1000;
}

impl FromStr for Dice {
    type Err = DiceParseError;

    fn from_str(line: &str) -> Result<Self, Self::Err> {
        let mut caps = DICE_RE.captures_iter(&line);
        let word = caps.next().ok_or(DiceParseError::Unparseable)?;
        Dice::try_from(word)
    }
}

impl TryFrom<Captures<'_>> for Dice {
    type Error = DiceParseError;

    fn try_from(cap: Captures) -> Result<Self, Self::Error> {
        let count = cap.name("count")
            .map(|m| m.as_str())
            .unwrap_or("1")
            .parse::<usize>().map_err(|_| DiceParseError::Unparseable)?;

        let sides_s = cap.name("sides")
            .map(|m| m.as_str())
            .ok_or(DiceParseError::Regex)?;
        let sides = if sides_s.to_lowercase() == "f" {
            0
        } else {
            let val = sides_s.parse().map_err(|_| DiceParseError::Unparseable)?;
            if val == 0 {
                return Err(DiceParseError::ZeroSides);
            }
            val
        };
        if sides > Self::SIDE_LIMIT {
            return Err(DiceParseError::TooManySides(sides));
        }

        //let hilo = if cap.name("hilo").is_some() {
        //    Self::get_lo_hi("hll", "hlh", &cap)?
        //} else if cap.name("lohi").is_some() {
        //    Self::get_lo_hi("lhl", "lhh", &cap)?
        //} else if cap.name("hihi").is_some() || cap.name("lolo").is_some() {
        //    Self::get_lo_hi("lo", "hi", &cap)?
        //} else {
        //    (Some(1), Some(sides))
        //};

        let keep = if let Some(updown) = cap.name("updown") {
            let amt = cap.name("amount").ok_or(DiceParseError::Regex)?
                .as_str()
                .parse::<isize>().map_err(|_| DiceParseError::Unparseable)?;
            match &*updown.as_str().to_lowercase() {
                "h" => amt,
                "l" => -amt,
                _ => return Err(DiceParseError::Regex),
            }
        } else {
            0
        };

        let fuse = if cap.name("exploding").is_some() {
            if let Some(fuse) = cap.name("fuse") {
                let fuse_s = fuse.as_str();
                let fuse_val = fuse_s.parse().map_err(|_| DiceParseError::Unparseable)?;
                if fuse_val <= 1 {
                    return Err(DiceParseError::ShortFuse);
                }
                fuse_val
            } else if sides > 1 {
                sides
            } else {
                return Err(DiceParseError::CannotExplode);
            }
        } else {
            0
        };

        Self::new_extended(count, sides, keep, fuse)
    }
}

#[cfg(test)]
pub mod test {
    use super::{Dice, DiceParseError};

    #[macro_export]
    macro_rules! expect_dice_similar {
        ($text: literal, $expect: expr) => {
            let parsed = $text.parse::<Dice>().unwrap();
            let provided = $expect.unwrap();
            expect_dice_similar!(parsed, provided)
        };
        ($d1: expr, $d2: expr) => {
            //println!("Comparing:\n\t{:?}\n\t{:?}", $d1, $d2);
            assert_eq!($d1.count(), $d2.count());
            assert_eq!($d1.sides(), $d2.sides());
            assert_eq!($d1.fuse(), $d2.fuse());
            if $d1.fuse() == 0 {
                assert_eq!($d1.rolls().len(), $d2.rolls().len());
            }
        };
    }

#[test]
    fn build_vs_new() {
        expect_dice_similar!("1d6", Dice::new_extended(1, 6, 0, 0));
        expect_dice_similar!("1d6!", Dice::new_exploding(1, 6, 6));
        expect_dice_similar!("1d6/H1", Dice::new_keep_n(1, 6, 1));
        expect_dice_similar!("1d6/L1", Dice::new_keep_n(1, 6, -1));
        expect_dice_similar!("1d6/L1!2", Dice::new_extended(1, 6, -1, 2));
        expect_dice_similar!("1d6", Some(Dice { count: 1, sides: 6, fuse: 0, rolls: vec![1], total: 1, keep: 0 }));
    }

#[test]
    fn r_1d6() {
        expect_dice_similar!("1d6", Dice::new_extended(1, 6, 0, 0));
    }

#[test]
    fn r_1d6_exploding() {
        expect_dice_similar!("1d6!", Dice::new_extended(1, 6, 0, 6));
    }

#[test]
    fn r_d6() {
        expect_dice_similar!("1d6", Dice::new_extended(1, 6, 0, 0));
    }

#[test]
    fn r_1df() {
        expect_dice_similar!("1df", Dice::new_extended(1, 0, 0, 0));
    }

#[test]
    fn r_1df_caps() {
        expect_dice_similar!("1DF", Dice::new_extended(1, 0, 0, 0));
    }

#[test]
    fn no_explode() {
        assert_eq!("1d1!".parse::<Dice>(), Err(DiceParseError::CannotExplode));
        assert_eq!("1df!".parse::<Dice>(), Err(DiceParseError::CannotExplode));
    }

#[test]
    fn roll_d1() {
        let roll = "3d1".parse::<Dice>().unwrap();
        assert_eq!(roll.sides, 1);
        assert_eq!(roll.total, 3);
    }

#[test]
    fn big_dice_bad() {
        assert_eq!("d1001".parse::<Dice>(), Err(DiceParseError::TooManySides(1001)));
        assert_eq!("1d1001".parse::<Dice>(), Err(DiceParseError::TooManySides(1001)));
        assert_eq!("101d10".parse::<Dice>(), Err(DiceParseError::TooManyDice(101)));
    }

#[test]
    fn keep_three_high() {
        let d = "4d6/h3".parse::<Dice>().unwrap();
        assert_eq!(d.rolls.len(), 4);
        assert_eq!(d.total, d.rolls[1..].to_vec().iter().fold(0, |acc, x| acc + (*x as i32)));
    }

#[test]
    fn keep_three_low() {
        let d = "4d6/L3".parse::<Dice>().unwrap();
        assert_eq!(d.rolls.len(), 4);
        assert_eq!(d.total, d.rolls[..3].to_vec().iter().fold(0, |acc, x| acc + (*x as i32)));
    }

#[test]
    fn two_keep_three_bad() {
        assert_eq!("2d20/H3".parse::<Dice>(), Err(DiceParseError::TooManyKept(3)));
    }

#[test]
    fn no_keep_d1() {
        assert_eq!("12d1/l3".parse::<Dice>(), Err(DiceParseError::TooManyKept(-3)));
    }

#[test]
    fn no_explode_1() {
        assert_eq!("1d5!1".parse::<Dice>(), Err(DiceParseError::ShortFuse));
        assert!("1d5!2".parse::<Dice>().is_ok());
    }
}
