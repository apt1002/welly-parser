use std::{io};

fn main() -> std::io::Result<()> {
    println!("Welly!");
    wparser::echo(&mut io::stdin().lock(), &mut io::stdout())?;
    Ok(())
}

