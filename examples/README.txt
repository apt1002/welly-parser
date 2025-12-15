I visited Dave Linton from 2025-10-12 to 2025-10-19 and we mocked up 
some bits of standard library in a recent dialect of Welly to see how it 
would go.

We invented traits and `impl` blocks.

We tried out the `throw` / `catch` style of control flow, but renamed it 
`match` / `case`. For the expression style we used `when TAG`, but I've changed
the syntax to `.TAG`.

We invented the syntax `OK[...]` for the type of a tagged union whose 
only tag is `OK`, and used `|` for type union.
