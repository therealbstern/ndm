// Copyright (C) 2021 Ben Stern
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::env;
use std::error::Error;
use std::fmt::Write;

use ndm::RollSet;

fn main() -> Result<(), Box<dyn Error>> {
    let args = env::args().collect::<Vec<String>>();
    let mut output = String::new();
    write!(&mut output, "{}", args[1..].join(" ").parse::<RollSet>()?)?;
    let safe = output.replace("\u{2122}", "-").replace("\u{21e8}", "=").replace("\u{00d7}", "x");
    println!("{}", safe);
    Ok(())
}
