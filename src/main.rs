use std::{io};
use io::{Write};

use welly_main::{ansi_term::Colour::{Blue}, Repl};
use welly_parser::{lexer, parse};

fn main() -> std::io::Result<()> {
    let lexer = lexer::Lexer::default();
    let mut stdin = io::stdin().lock();
    let mut stdout = io::stdout();
    let mut repl = Repl::default();
    while !repl.is_complete {
        writeln!(stdout, "\nWelly!")?;
        if let Some(stmts) = repl.command(&mut stdin, &mut stdout, |command| parse(&lexer, command))? {
            for stmt in stmts {
                let stmt_output = format!("{:#?}", stmt);
                writeln!(stdout, "{}", Blue.paint(stmt_output))?;
            }
        }
    }
    Ok(())
}
