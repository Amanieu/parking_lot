// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::env;
use std::process;

#[derive(Copy, Clone)]
pub struct ArgRange {
    current: usize,
    limit: usize,
    step: usize,
}

impl ArgRange {
    pub fn is_single(&self) -> bool {
        self.current.saturating_add(self.step) > self.limit
    }
}

impl Iterator for ArgRange {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        if self.current <= self.limit {
            let result = self.current;
            self.current = self.current.saturating_add(self.step);
            Some(result)
        } else {
            None
        }
    }
}

fn print_usage(names: &[&str], error_msg: Option<String>) -> ! {
    if let Some(error) = error_msg {
        println!("{}", error);
    }
    println!("Usage: {} {}", env::args().next().unwrap(), names.join(" "));
    println!(
        "Each argument can be a single value or a range in the form start:end or \
         start:end:step"
    );
    process::exit(1);
}

fn parse_num(names: &[&str], name: &str, value: &str) -> usize {
    value.parse().unwrap_or_else(|_| {
        print_usage(
            names,
            Some(format!("Invalid value for {}: {}", name, value)),
        )
    })
}

fn parse_one(names: &[&str], name: &str, value: &str) -> ArgRange {
    let components = value.split(':').collect::<Vec<_>>();
    match components.len() {
        1 => {
            let val = parse_num(names, name, components[0]);
            ArgRange {
                current: val,
                limit: val,
                step: 1,
            }
        }
        2 => {
            let start = parse_num(names, name, components[0]);
            let end = parse_num(names, name, components[1]);
            if start > end {
                print_usage(
                    names,
                    Some(format!("Invalid range for {}: {}", name, value)),
                );
            }
            ArgRange {
                current: start,
                limit: end,
                step: 1,
            }
        }
        3 => {
            let start = parse_num(names, name, components[0]);
            let end = parse_num(names, name, components[1]);
            let step = parse_num(names, name, components[2]);
            if start > end {
                print_usage(
                    names,
                    Some(format!("Invalid range for {}: {}", name, value)),
                );
            }
            ArgRange {
                current: start,
                limit: end,
                step: step,
            }
        }
        _ => print_usage(
            names,
            Some(format!("Invalid value for {}: {}", name, value)),
        ),
    }
}

pub fn parse(names: &[&str]) -> Vec<ArgRange> {
    let args = env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() {
        print_usage(names, None);
    }
    if args.len() != names.len() {
        print_usage(
            names,
            Some(format!(
                "Invalid number of arguments (expected {}, got {})",
                names.len(),
                args.len()
            )),
        );
    }

    let mut result = vec![];
    for (name, value) in names.iter().zip(args) {
        result.push(parse_one(names, name, &value));
    }
    result
}
