#[allow(unused_macros)]
#[macro_use]
mod language;
mod model;
mod parser;
#[allow(unused_macros)]
#[macro_use]
mod proof;
mod solver;
mod tokenizer;
extern crate clap;
use clap::{App, Arg, SubCommand};

fn main() {
    let app = App::new("rfol")
        .version("0.0.0")
        .author("kalgr <hoge@fuga.com>")
        .about("RFOL CLI")
        .subcommand(
            SubCommand::with_name("refute")
                .about("echo input formula")
                .arg(
                    Arg::with_name("input")
                        .help("input formula in Polish notation")
                        .short("i")
                        .long("input")
                        .takes_value(true)
                        .required(true),
                )
                .arg(
                    Arg::with_name("max_domain_size")
                        .help("maximum domain size to search")
                        .long("max_domain_size")
                        .takes_value(true)
                        .default_value("8")
                        .required(true),
                ),
        )
        .subcommand(
            SubCommand::with_name("prove_lk")
                .about("echo input formula")
                .arg(
                    Arg::with_name("input")
                        .help("input formula in Polish notation")
                        .short("i")
                        .long("input")
                        .takes_value(true)
                        .required(true),
                )
                .arg(
                    Arg::with_name("max_proof_depth")
                        .help("maximum proof depth to search")
                        .short("d")
                        .long("max_proof_depth")
                        .takes_value(true)
                        .default_value("8")
                        .required(true),
                )
                .arg(
                    Arg::with_name("use_cut")
                        .help("include cut rule in proofs to be searched")
                        .short("c")
                        .long("use_cut"),
                ),
        );

    let matches = app.get_matches();

    if let Some(ref matches) = matches.subcommand_matches("refute") {
        if let (Some(fml), Some(max_domain_size_str)) = (
            matches.value_of("input"),
            matches.value_of("max_domain_size"),
        ) {
            let max_domain_size: u32 = max_domain_size_str.parse().unwrap();
            use tokenizer::Tokenizer;
            let mut tokenizer = Tokenizer::new();
            let fml = tokenizer.tokenize(fml);
            use parser::*;
            let mut parser = Parser::new();
            match parser.parse(&fml) {
                Ok(fml) => {
                    println!("{:?}", fml);
                    use solver::*;
                    if let Some(model) = refute_on_finite_models(fml, max_domain_size) {
                        println!("{:?}", model);
                    } else {
                        println!("No refutation model found.");
                    }
                }
                Err(s) => println!("{:?}", s),
            }
        }
    } else if let Some(ref matches) = matches.subcommand_matches("prove_lk") {
        if let (Some(fml), Some(max_proof_depth_str)) = (
            matches.value_of("input"),
            matches.value_of("max_proof_depth"),
        ) {
            let max_proof_depth: u32 = max_proof_depth_str.parse().unwrap();
            use tokenizer::Tokenizer;
            let mut tokenizer = Tokenizer::new();
            let fml = tokenizer.tokenize(fml);
            use parser::*;
            let mut parser = Parser::new();
            match parser.parse(&fml) {
                Ok(fml) => {
                    use solver::*;
                    let use_cut = matches.is_present("use_cut");
                    if let Ok(proof) = prove_with_lk(fml, max_proof_depth, use_cut) {
                        println!("{}", proof);
                    } else {
                        println!("No proof found.");
                    }
                }
                Err(s) => println!("{}", s),
            }
        }
    }
}
