// Copyright (C) 2021 Ben Stern
// SPDX-License-Identifier: MIT OR Apache-2.0

#![forbid(unsafe_code)]

//! Parses dice notation, and evaluate algebraic manipulation of sets of dice
//! rolls.
//!
//! This module provides [Dice] and [RollSet] structs, which implement
//! [std::str::FromStr] for converting from strings.  It also provides error
//! types directly related to parsing dice-related strings.
//!
//! # Examples
//!
//! ## Dice Examples
//!
//! ### Rolling Dice
//!
//! Creating [Dice] from a string literal:
//!
//! ```
//! use ndm::Dice;
//!
//! let d6 = "1d6".parse::<Dice>().unwrap();
//! ```
//!
//! You can create them directly:
//!
//! ```
//! use ndm::Dice;
//!
//! let d4 = Dice::new(1, 4);
//! ```
//!
//! ### Exploding Dice
//!
//! Creating exploding dice (which roll again when the highest number is
//! rolled):
//!
//! ```
//! use ndm::Dice;
//!
//! let exploding_d20 = "1d20!".parse::<Dice>().unwrap();
//! let exploding_d6 = Dice::new_exploding(1, 6, 6);
//! ```
//!
//! Exploding dice can explode on any number greater than 1:
//!
//! ```
//! use ndm::Dice;
//!
//! let exploding_d13 = "1d13!2".parse::<Dice>().unwrap();
//! ```
//!
//! ### More Complicated Examples
//!
//! Rolling multiple [Dice] at a time:
//!
//! ```
//! use ndm::Dice;
//!
//! let dice = Dice::new(3, 8);
//! let dice = Dice::new_exploding(2, 4, 4);
//! ```
//!
//! ### Keeping High or Low Rolls
//! 
//! Keeping the three highest dice:
//!
//! ```
//! use ndm::Dice;
//!
//! let wis = Dice::new_keep_n(4, 6, 3);
//! let dex: Dice = "4d6/H3".parse().unwrap();
//! ```
//!
//! Or the lowest roll:
//!
//! ```
//! use ndm::Dice;
//!
//! let disadvantage = Dice::new_keep_n(2, 20, -1);
//! let minimum: Dice = "4d7/L1".parse().unwrap();
//! ```
//!
//! (String parsing isn't case-sensitive.)
//!
//! Keeping exploding dice:
//!
//! ```
//! use ndm::Dice;
//!
//! let dice = Dice::new_extended(4, 7, 5, 3);
//! // or
//! let dice = "4d7/H3!5".parse::<Dice>().unwrap();
//! ```
//!
//! ### Formatting Dice
//!
//! [Dice] can be formatted with the normal `{}` operator:
//!
//! ```
//! use ndm::Dice;
//!
//! println!("{}", Dice::new(2, 10).unwrap());
//! ```
//!
//! ### Parse Errors
//!
//! Strings which cannot be parsed cause [DiceParseError]s.  String parsing is
//! more strict than the constructors, which currently don't fail, but instead
//! ignore invalid parameters.
//!
//! ## Combinations
//!
//! Sets of dice, such as multiple sizes of dice, and mathematical operations
//! upon dice, are represented by [RollSet]s.
//!
//! `RollSet`s can only be created by parsing string slices:
//!
//! ```
//! use ndm::RollSet;
//!
//! let roll_set: RollSet = "3d6".parse().unwrap();
//! ```
//!
//! `RollSet`s can contain any combinations of valid [Dice] and whole numbers,
//! joined by `+` or `-` (or &#x2212;).  These combinations can also be
//! multiplied by floating-point numbers, using `*` (or `x` or `X` or &#x00d7;).
//!
//! ```
//! use ndm::RollSet;
//!
//! let roll_set: RollSet = "1d20+4".parse().unwrap();
//! let empowered = "4d6 * 1.5".parse::<RollSet>().unwrap();
//! let sneak = "3d8 + 2d6".parse::<RollSet>().unwrap();
//! ```
//!
//! Extraneous text can be included:
//!
//! ```
//! use ndm::RollSet;
//!
//! let roll_set = "2d8 slashing + 3d6 fire".parse::<RollSet>().unwrap();
//! ```
//!
//! End-comments can be indicated by `#`, which will prevent additional parsing:
//!
//! ```
//! use ndm::RollSet;
//!
//! // Only the 4d6 will be parsed, the 8d6 is just a comment.
//! let roll_set: RollSet = "4d6 # 8d6 on a critical".parse().unwrap();
//! ```
//!
//! [RollSet]s can also be formatted using `{}`, and totals will appear before
//! an end-of-line comment, if any.
//!
//! ```
//! use ndm::RollSet;
//!
//! // Prints something like: `3d6 [ 2, 4, 5: 11] slashing + 4 = 15`
//! println!("{}", "3d6 slashing + 4".parse::<RollSet>().unwrap());
//! // Prints something like `3d6 [ 3, 5, 6: 14] + 4 = 18 # slashing`
//! println!("{}", "3d6+4 # slashing".parse::<RollSet>().unwrap());
//! ```
//!
//! ### Parse Errors
//!
//! Errors are returned using [RollParseError].  In general, [RollSet]s treat
//! anything that isn't [Dice], operators, or numbers as comments, but will fail
//! if there isn't a roll anywhere in the string.  Some combinations of
//! operators are also invalid: [Dice] can't be multiplied by other `Dice`, text
//! can't be added to numbers, etc.
//!
//! # More Information
//!
//! Dice math is from left to right, regardless of operator.  For example,
//! `4d6 + 12 * 1.5` ranges from 24 ((4 + 12) * 1.5) to 54 ((24 + 12) * 1.5),
//! not from 22 to 42.
//!
//! Addition and subtraction can be done with whole numbers, dice rolls, and
//! results of previous operations.  Multiplication can be done upon all of the
//! above, but the right hand side must be a number (either whole or
//! floating-point).  Also, the result of floating-point math is truncated:
//! `1d6 * 4.9` ranges from 4 to 29, not from 4.9 to 29.4.
//!
//! Exploding dice get rerolled as long as they roll at least as high as the
//! &ldquo;fuse&rdquo; (which defaults to the highest value on the die, but may
//! be as low as 2).
//!
//! You can construct [Dice] directly, or complex expressions of
//! [RollSet]s.
//!
//! The dice notation parsed by this library is:
//!
//! \[count\]`d`&lt;sides&gt;\[`/`&lt;`H`|`L`&gt;&lt;keep&gt;\]\[`!`\[fuse\]\]
//!
//! - `count` is the number of dice to roll, is optional, and defaults to 1
//! - `sides` is the number of sides on the dice and is required
//!   - If numeric, it must be non-negative
//!   - `f` or `F` may be used to represent [Fudge/Fate](https://en.wikipedia.org/wiki/Fudge_(role-playing_game_system)#Fudge_dice) dice
//! - Optionally, `/`, followed by
//!   - `H` (or `h`) or `L` (or `l`) and
//!   - a positive number less than or equal to the number of dice rolled
//! - Optionally, `!`, optionally followed by the `fuse` as a whole number
//!   - If the fuse is provided, it must be at least 2
//!   - Otherwise, it defaults to the highest possible roll for the die
//!
//! Dice can be added with `+`, subtracted with `-` [or &minus;], or multiplied
//! with '*' [or `x` or `&times;`].  Other text is treated as comments.
//!
//! [Dice] can be combined with each other by addition or subtraction.  You can
//! also add or subtract whole numbers and multiply results by floating point
//! numbers.  (Division isn't currently supported directly, but you can multiply
//! by the reciprocal.)

mod dice;
mod rollset;

pub use dice::{Dice as Dice, DiceParseError as DiceParseError};
pub use rollset::{RollParseError as RollParseError, RollSet as RollSet};
