use std::{io};

fn main() -> std::io::Result<()> {
    println!("Welly!");
    welly_parser::echo(&mut io::stdin().lock(), &mut io::stdout())?;
    Ok(())
}

