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
    /// An attempt was made to create zero dice.
    ZeroCount,
    /// A fuse of 1 was provided; such a fuse would always explode.
    ShortFuse,
    /// An impossible fuse was provided; such a fuse would never explode and
    /// indicates a logic error.
    LongFuse(u16),
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

    /// Roll (simple) dice.  Dice are rolled at creation time and not
    /// otherwise modified.
    ///
    /// - `n` is the number of dice and must be non-zero
    /// - `m` is the number of sides; zero (0) is treated as a request to create [Fudge/Fate](https://en.wikipedia.org/wiki/Fudge_(role-playing_game_system)#Fudge_dice) dice
    ///
    /// Dice created this way don't explode and are all kept.
    ///
    /// ```
    /// use ndm::Dice;
    ///
    /// // create 1d6
    /// let d6 = Dice::new(1, 6);
    /// ```
    pub fn new(n: usize, m: u16) -> Result<Self, DiceParseError> {
        Dice::new_extended(n, m, 0, 0)
    }

    /// Roll "exploding" dice.  Dice are rolled at creation time and not
    /// otherwise modified.
    ///
    /// Any die which is rolls a value greater than or
    /// equal to `fuse` will be added to the total and rolled again.
    ///
    /// Dice created this way are all kept.
    ///
    /// One-sided dice can't explode, because if they did, they would never
    /// stop.  [Fudge/Fate](https://en.wikipedia.org/wiki/Fudge_(role-playing_game_system)#Fudge_dice)
    /// dice can't explode either, because it doesn't make sense for them to.
    ///
    /// ```
    /// use ndm::Dice;
    ///
    /// // create 1d6
    /// let d6_explode_5 = Dice::new_exploding(1, 6, 5);
    /// ```
    pub fn new_exploding(count: usize, sides: u16, fuse: u16) -> Result<Self, DiceParseError> {
        Dice::new_extended(count, sides, 0, fuse)
    }

    /// Roll dice, adding only the highest or lowest `n` rolls to the total.
    /// Dice are rolled at creation time and not otherwise modified.
    ///
    /// If `n` < 0, the `n` lowest dice are kept.  If `n` > 0, the `n` highest
    /// dice are kept.  If `n` == 0, all dice are kept.
    ///
    /// Dice created this way don't explode.
    ///
    /// ```
    /// use ndm::Dice;
    ///
    /// // Roll 4 six-sided dice, keeping the highest 3.
    /// let wis = Dice::new_keep_n(4, 6, 3);
    /// // Roll 2 twenty-sided dice, keeping the lower roll.
    /// let disadvantage = Dice::new_keep_n(2, 20, -1);
    /// ```
    pub fn new_keep_n(count: usize, sides: u16, n: isize) -> Result<Self, DiceParseError> {
        Dice::new_extended(count, sides, n, 0)
    }

    /// Roll dice which may explode and optionally use some of the dice
    /// when calculating the total.
    /// Dice are rolled at creation time and not otherwise modified.
    ///
    /// If `keep` < 0, the `keep` lowest dice are kept.  If `keep` > 0, the
    /// `keep` highest dice are kept.  If `keep` == 0, all dice are kept.
    ///
    /// Any die which is rolls a value greater than or
    /// equal to `fuse` will be added to the total and rolled again.
    ///
    /// One-sided dice can't explode, because if they did, they would never
    /// stop.  [Fudge/Fate](https://en.wikipedia.org/wiki/Fudge_(role-playing_game_system)#Fudge_dice)
    /// dice can't explode either, because it doesn't make sense for them to.
    ///
    /// ```
    /// use ndm::Dice;
    ///
    /// // Roll 8 sixteen-sided dice, keeping the highest 3 but exploding on 4 or
    /// // higher.
    /// let dice = Dice::new_extended(8, 16, 3, 4);
    /// ```
    pub fn new_extended(count: usize, sides: u16, keep: isize, fuse: u16) -> Result<Self, DiceParseError> {
        //println!("Called with count: {}, sides: {}, keep: {}, fuse: {}", count, sides, keep, fuse);
        if sides > Self::SIDES_LIMIT {
            return Err(DiceParseError::TooManySides(sides));
        } else if (sides < 2) && (fuse != 0) {
            return Err(DiceParseError::CannotExplode);
        }

        if count > Self::COUNT_LIMIT {
            return Err(DiceParseError::TooManyDice(count));
        } else if count == 0 {
            return Err(DiceParseError::ZeroCount);
        }

        if fuse == 1 {
            return Err(DiceParseError::ShortFuse);
        } else if fuse > sides {
            return Err(DiceParseError::LongFuse(fuse));
        }

        if (keep < 0) && (count < ((-keep) as usize)) {
            return Err(DiceParseError::TooManyKept(keep));
        } else if (keep > 0) && (count < (keep as usize)) {
            return Err(DiceParseError::TooManyKept(keep));
        }

        let mut rolls: Vec<u16>;
        let mut rng = thread_rng();

        let total = match sides {
            0 => {
                rolls = vec![0; 3];
                for _ in 0 .. count {
                    let last_roll = rng.gen_range(0 ..= 2);
                    rolls[last_roll as usize] += 1;
                }
                // This is an optimization for the way Fate dice are stored and
                // is therefore suspect as premature.  On the other hand, it
                // works (and there's a test for it).
                match keep.cmp(&0) {
                    Ordering::Less => {
                        if rolls[0] as isize >= -keep {
                            keep as i32
                        } else if (rolls[0] + rolls[1]) as isize >= -keep {
                            -(rolls[0] as i32)
                        } else {
                            (-keep as i32) - (rolls[1] as i32) - 2 * (rolls[0] as i32)
                        }
                    },
                    Ordering::Greater => {
                        if rolls[2] as isize >= keep {
                            keep as i32
                        } else if (rolls[1] + rolls[2]) as isize >= keep {
                            rolls[2] as i32
                        } else {
                            (-keep as i32) + (rolls[1] as i32) + 2 * (rolls[2] as i32) as i32
                        }
                    },
                    Ordering::Equal => (rolls[2] as i32) - (rolls[0] as i32)
                }
            },
            1 => {
                rolls = Vec::with_capacity(0);
                match keep.cmp(&0) {                                                                                                 
                    Ordering::Less => -keep as i32,
                    Ordering::Greater => keep as i32,
                    Ordering::Equal => count as i32,
                }
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
                    Ordering::Less => 0 .. (-keep as usize),
                    Ordering::Greater => rolls.len() - (keep as usize) .. rolls.len(),
                    Ordering::Equal => 0 .. rolls.len(),
                };

                rolls[range].iter().map(|&x| x as i32).sum()
            }
        };
        Ok(Dice { count, sides, fuse, rolls, keep, total })
    }

    /// The net value of this roll (after dropping any dice that weren't [kept]
    /// and adding any that met or exceeded the [fuse]).
    pub fn total(&self) -> i32 { self.total }

    /// The number of sides on the dice.  Fate/Fudge dice have zero (0) sides.
    pub fn sides(&self) -> u16 { self.sides }

    /// The number of dice requested.  This may differ from the number of dice
    /// rolled (as returned by [rolls] and [all_rolls] if any dice exploded (see
    /// [fuse]), or if any weren't kept (see [kept]).  This will always be at
    /// least one (1).
    pub fn count(&self) -> usize { self.count }

    /// The [kept] rolls.  This may be less than the number of dice requested if
    /// some weren't kept, or more if some rolls met or exceeded the [fuse].
    /// See [all_rolls] for all dice rolled.
    ///
    /// There are two special cases:
    /// * Fudge/Fate dice always return a reference to a [Vec] of length 3:
    ///   * `[0]` is the number of minuses or failures
    ///   * `[1]` is the number of zeroes or neutral results
    ///   * `[2]` is the number of pluses or successes
    /// * One-sided dice (d1) always return an empty [Vec], since they can't
    ///   roll anything but a one (1).
    ///
    /// Note that neither Fudge/Fate dice nor `d1`s can "explode".  Also note
    /// that for these dice, the [total] is usually the most interesting value.
    pub fn rolls(&self) -> &[u16] {
        if self.sides > 1 {
            match self.keep.cmp(&0) {
                Ordering::Less => &self.rolls[0 .. (-self.keep as usize)],
                Ordering::Greater => &self.rolls[self.rolls.len() - (self.keep as usize) .. self.rolls.len()],
                Ordering::Equal => &self.rolls,
            }
        } else {
            self.all_rolls()
        }
    }

    /// All dice rolled, including any dice that weren't [kept] in the total.
    /// This may differ from the [count] if any dice met or exceeded the [fuse].
    ///
    /// There are two special cases:
    /// * Fudge/Fate dice always return a reference to a [Vec] of length 3:
    ///   * `[0]` is the number of minuses or failures
    ///   * `[1]` is the number of zeroes or neutral results
    ///   * `[2]` is the number of pluses or successes
    /// * One-sided dice (d1) always return an empty [Vec], since they can't
    ///   roll anything but a one (1).
    ///
    /// Note that neither Fudge/Fate dice nor `d1`s can "explode".
    /// Also note that for one-sided dice, the [count] and the [total] are
    /// usually more useful data.
    pub fn all_rolls(&self) -> &Vec<u16> { &self.rolls }

    /// The number upon which dice "exploded", triggering a re-roll.
    /// Zero (0) means the dice couldn't explode.
    pub fn fuse(&self) -> u16 { self.fuse }

    /// Indicates whether any dice actually exploded.  This is a utility method
    /// as the semantics of measuring how many dice were rolled is not trivially
    /// derivable from [all_rolls].  Note that neither Fudge/Fate dice nor `d1`s
    /// can explode.
    pub fn exploded(&self) -> bool {
        (self.sides >= 2) && (self.fuse != 0) && (self.rolls.len() > self.count)
    }

    /// The number of dice kept when calculating the [total] of this roll.
    pub fn kept(&self) -> isize { self.keep }
}

impl Display for Dice {
    /// The output format for [Dice] is currently unstable but considered
    /// human-readable.
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FmtError> {
        write!(fmt, "{}d{}", self.count, self.sides)?;
        if self.fuse > 1 {
            write!(fmt, "!")?;
            if self.fuse != self.sides {
                write!(fmt, "{}", self.fuse)?;
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
    fn keep_d1() {
        assert_eq!("12d1/l3".parse::<Dice>(), Dice::new_keep_n(12, 1, -3));
        assert_eq!("12d1/h3".parse::<Dice>(), Dice::new_keep_n(12, 1, 3));

        let d = "12d1/h3".parse::<Dice>().unwrap();
        assert_eq!(d.total, 3);
        let d = "12d1/l3".parse::<Dice>().unwrap();
        assert_eq!(d.total, 3);
    }

    #[test]
    fn keep_df() {
        expect_dice_similar!("12df/l3", Dice::new_keep_n(12, 0, -3));
        expect_dice_similar!("12dF/h3", Dice::new_keep_n(12, 0, 3));

        let d = "12df/h3".parse::<Dice>().unwrap();
        assert_eq!(d.kept(), 3);
    }

    #[test]
    fn no_explode_1() {
        assert_eq!("1d5!1".parse::<Dice>(), Err(DiceParseError::ShortFuse));
        assert!("1d5!2".parse::<Dice>().is_ok());
    }

    fn calc_short_keep(rolls: &Vec<i32>, keep: isize) -> i32 {
        use std::cmp::Ordering;

        match keep.cmp(&0) {
            Ordering::Less => {
                if rolls[0] as isize >= -keep {
                    keep as i32
                } else if (rolls[0] + rolls[1]) as isize >= -keep {
                    -(rolls[0] as i32)
                } else {
                    (-keep as i32) - (rolls[1] as i32) - 2 * (rolls[0] as i32)
                }
            },
            Ordering::Greater => {
                if rolls[2] as isize >= keep {
                    keep as i32
                } else if (rolls[1] + rolls[2]) as isize >= keep {
                    rolls[2] as i32
                } else {
                    (-keep as i32) + (rolls[1] as i32) + 2 * (rolls[2] as i32) as i32
                }
            },
            Ordering::Equal => (rolls[2] as i32) - (rolls[0] as i32)
        }
    }

    fn calc_long_keep(rolls: &Vec<i32>, keep: isize) -> i32 {
        use std::cmp::Ordering;

        let range = match keep.cmp(&0) {
            Ordering::Less => 0 .. (-keep as usize),
            Ordering::Greater => rolls.len() - (keep as usize) .. rolls.len(),
            Ordering::Equal => 0 .. rolls.len(),
        };
        rolls[range].iter().map(|&x| x as i32).sum()
    }

    #[test]
    fn fate_keepers() {
        // N.B., doubling EXP increases the runtime of this test by a factor of
        // 10 (the runtime is exponential over LIMIT)
        const EXP: u32 = 5;
        let limit = 3usize.pow(EXP);

        for i in 0 .. limit {
            let mut short_rolls = vec![0i32; 3];
            let mut long_rolls = vec![0i32; EXP as usize];
            let mut ctr = i;
            for j in 0 .. EXP as usize {
                short_rolls[ctr % 3] += 1;
                long_rolls[j] = (ctr % 3) as i32 - 1;
                ctr /= 3;
            }
            long_rolls.sort_unstable();
            for keep in -(EXP as isize) ..= EXP as isize {
                assert_eq!(calc_short_keep(&short_rolls, keep), calc_long_keep(&long_rolls, keep));
            }
        }
    }
}
