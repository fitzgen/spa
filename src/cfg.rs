//! Intermediate representation.
//!
//! Our IR is a control flow graph composed of linear basic blocks consisting of
//! RISC-style instructions for an idealized machine with an infinite number of
//! registers. Each instruction produces its result in a specified register,
//! rather than overwriting one of its operands.
//!
//! When lowering the AST into the IR, we use a fresh temporary register for
//! each intermediate result. We leave it to future code improvement passes to
//! cut down on the number of registers in use at any given time, and the
//! register spills implied.

use ast;
use std::collections::HashMap;

/// A register is either an identifier from the source, or a temporary
/// intermediate result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Register<'a> {
    Identifier(ast::Identifier<'a>),
    Temp(usize),
}

impl<'a> From<ast::Identifier<'a>> for Register<'a> {
    fn from(id: ast::Identifier<'a>) -> Self {
        Register::Identifier(id)
    }
}

/// A label pointing to the start of a basic block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Label(usize);

/// A basic block.
///
/// A basic block is a linear sequence of instructions that may only be entered
/// at its head, and only exits at its tail. There are no early exits nor jumps
/// into the middle of the block.
#[derive(Debug, PartialEq, Eq)]
pub struct BasicBlock<'a> {
    label: Label,
    instructions: Vec<Instruction<'a>>,
}

impl<'a> BasicBlock<'a> {
    /// Get the label pointing to the start of this block.
    pub fn label(&self) -> Label {
        self.label
    }

    /// Get this block's instructions.
    pub fn instructions(&self) -> &[Instruction<'a>] {
        &self.instructions[..]
    }

    fn is_empty(&self) -> bool {
        self.instructions.is_empty()
    }

    fn push(&mut self, insn: Instruction<'a>) {
        self.instructions.push(insn);
    }
}

/// An instruction for our idealized machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instruction<'a> {
    /// `r = input`
    Input(Register<'a>),

    /// `print r`
    Output(Register<'a>),

    /// `r = malloc`
    Malloc(Register<'a>),

    /// `r = null`
    Null(Register<'a>),

    /// `r1 = *r2`
    Deref(Register<'a>, Register<'a>),

    /// `r = n`
    Int(Register<'a>, isize),

    /// `r1 = r2 + r3`
    Add(Register<'a>, Register<'a>, Register<'a>),

    /// `r1 = r2 - r3`
    Sub(Register<'a>, Register<'a>, Register<'a>),

    /// `r1 = r2 * r3`
    Mul(Register<'a>, Register<'a>, Register<'a>),

    /// `r1 = r2 / r3`
    Div(Register<'a>, Register<'a>, Register<'a>),

    /// `r1 = r2 == r3`
    Eq(Register<'a>, Register<'a>, Register<'a>),

    /// `r1 = r2 > r3`
    Gt(Register<'a>, Register<'a>, Register<'a>),

    /// `r1 = !r2`
    Not(Register<'a>, Register<'a>),

    /// `r1 = f(r...)`
    Call(Register<'a>, ast::Identifier<'a>, Vec<Register<'a>>),

    /// `r1 = (*r2)(r...)`
    Indirect(Register<'a>, Register<'a>, Vec<Register<'a>>),

    /// `r1 = &r2`
    Addr(Register<'a>, Register<'a>),

    /// `r1 = r2`
    Mov(Register<'a>, Register<'a>),

    /// May only occur at the end of a basic block.
    ///
    /// `return r`
    Return(Register<'a>),

    /// May only occur at the end of a basic block.
    ///
    /// `if r { goto l1 } else { goto l2 }`
    Branch(Register<'a>, Label, Label),

    /// May only occur at the end of a basic block.
    ///
    /// `goto l`
    Jump(Label),
}

/// The context built up when lowering the AST to our IR.
///
/// This contains the control flow graph and its basic blocks, as well as
/// metadata about each function, their entry labels and frame sizes (number of
/// registers used).
#[derive(Debug, Default)]
pub struct Context<'a> {
    blocks: Vec<Option<BasicBlock<'a>>>,
    register_counter: usize,

    // The entry label and number of registers each function uses.
    functions: HashMap<ast::Identifier<'a>, (Label, usize)>,
}

impl<'a> Context<'a> {
    /// Create a new, incomplete basic block.
    ///
    /// This leaves an incomplete block entry at the new block's label. Upon
    /// finishing construction of the block, we must pass it back to one of the
    /// `finish_block_*` functions which will mark the block entry complete.
    fn new_block(&mut self) -> BasicBlock<'a> {
        let label = Label(self.blocks.len());
        self.blocks.push(None);
        BasicBlock {
            label,
            instructions: vec![],
        }
    }

    /// Finish constructing a basic block with a return.
    fn finish_block_with_return(&mut self, mut block: BasicBlock<'a>, reg: Register<'a>) {
        let label = block.label();
        assert!(self.blocks[label.0].is_none());
        block.push(Instruction::Return(reg));
        self.blocks[label.0] = Some(block);
    }

    /// Finish constructing a basic block with a branch.
    fn finish_block_with_branch(
        &mut self,
        mut block: BasicBlock<'a>,
        reg: Register<'a>,
        consequent: Label,
        alternative: Label,
    ) {
        let label = block.label();
        assert!(self.blocks[label.0].is_none());
        block.push(Instruction::Branch(reg, consequent, alternative));
        self.blocks[label.0] = Some(block);
    }

    /// Finish constructing a basic block with a jump.
    fn finish_block_with_jump(&mut self, mut block: BasicBlock<'a>, to: Label) {
        let label = block.label();
        assert!(self.blocks[label.0].is_none());
        block.push(Instruction::Jump(to));
        self.blocks[label.0] = Some(block);
    }

    /// Get a new temporary register.
    fn new_register(&mut self) -> Register<'a> {
        let r = Register::Temp(self.register_counter);
        self.register_counter += 1;
        r
    }
}

/// Traversal of the AST, lowering it to our IR.
pub trait Lower<'a, 'b>
where
    'a: 'b,
{
    /// If the `Self` type needs some extra argument during lowering, it can
    /// specify it with this associated type. Otherwise, `Arg` can be set to
    /// `()` and ignored.
    type Arg;

    /// If the `Self` type needs to convey information about its lowering to its
    /// caller, then it can return it via this associated type. Otherwise, `Arg`
    /// can be set to `()` and ignored.
    type Ret;

    /// Lower `self` into our IR.
    fn lower(&self, ctx: &mut Context<'a>, extra: Self::Arg) -> Self::Ret;
}

impl<'a, 'b> Lower<'a, 'b> for ast::Expression<'a>
where
    'a: 'b,
{
    // We need access to the basic block we are lowering this expression into.
    type Arg = &'b mut BasicBlock<'a>;

    // We need to tell our caller what register contains the result of this
    // expression, so that it can use it to further the computation.
    type Ret = Register<'a>;

    fn lower(&self, ctx: &mut Context<'a>, block: &'b mut BasicBlock<'a>) -> Register<'a> {
        match *self {
            ast::Expression::Input => {
                let r = ctx.new_register();
                block.push(Instruction::Input(r));
                r
            }
            ast::Expression::Malloc => {
                let r = ctx.new_register();
                block.push(Instruction::Malloc(r));
                r
            }
            ast::Expression::Null => {
                let r = ctx.new_register();
                block.push(Instruction::Null(r));
                r
            }
            ast::Expression::Deref(ref expr) => {
                let p = expr.lower(ctx, block);
                let r = ctx.new_register();
                block.push(Instruction::Deref(r, p));
                r
            }
            ast::Expression::Integer(n) => {
                let r = ctx.new_register();
                block.push(Instruction::Int(r, n));
                r
            }
            ast::Expression::Identifier(id) => id.into(),
            ast::Expression::Addition(ref exprs) => {
                let p = exprs[0].lower(ctx, block);
                let q = exprs[1].lower(ctx, block);
                let r = ctx.new_register();
                block.push(Instruction::Add(r, p, q));
                r
            }
            ast::Expression::Subtraction(ref exprs) => {
                let p = exprs[0].lower(ctx, block);
                let q = exprs[1].lower(ctx, block);
                let r = ctx.new_register();
                block.push(Instruction::Sub(r, p, q));
                r
            }
            ast::Expression::Multiplication(ref exprs) => {
                let p = exprs[0].lower(ctx, block);
                let q = exprs[1].lower(ctx, block);
                let r = ctx.new_register();
                block.push(Instruction::Mul(r, p, q));
                r
            }
            ast::Expression::Division(ref exprs) => {
                let p = exprs[0].lower(ctx, block);
                let q = exprs[1].lower(ctx, block);
                let r = ctx.new_register();
                block.push(Instruction::Div(r, p, q));
                r
            }
            ast::Expression::Equal(ref exprs) => {
                let p = exprs[0].lower(ctx, block);
                let q = exprs[1].lower(ctx, block);
                let r = ctx.new_register();
                block.push(Instruction::Eq(r, p, q));
                r
            }
            ast::Expression::Greater(ref exprs) => {
                let p = exprs[0].lower(ctx, block);
                let q = exprs[1].lower(ctx, block);
                let r = ctx.new_register();
                block.push(Instruction::Gt(r, p, q));
                r
            }
            ast::Expression::Negation(ref expr) => {
                let q = expr.lower(ctx, block);
                let r = ctx.new_register();
                block.push(Instruction::Not(r, q));
                r
            }
            ast::Expression::Call(f, ref args) => {
                let args = args.iter().map(|a| a.lower(ctx, block)).collect();
                let r = ctx.new_register();
                block.push(Instruction::Call(r, f, args));
                r
            }
            ast::Expression::IndirectCall(ref expr, ref args) => {
                let who = expr.lower(ctx, block);
                let args = args.iter().map(|a| a.lower(ctx, block)).collect();
                let r = ctx.new_register();
                block.push(Instruction::Indirect(r, who, args));
                r
            }
            ast::Expression::AddressOf(id) => {
                let r = ctx.new_register();
                block.push(Instruction::Addr(r, id.into()));
                r
            }
        }
    }
}

impl<'a, 'b> Lower<'a, 'b> for ast::Statement<'a>
where
    'a: 'b,
{
    // Statements might append to the current basic block, or they might finish
    // the current basic block and create new ones. Therefore, we can't take a
    // mutable reference to a block, like Expression does, and instead take and
    // return the current block itself (and the returned current block may be
    // different than the input current block).
    type Arg = BasicBlock<'a>;
    type Ret = BasicBlock<'a>;

    fn lower(&self, ctx: &mut Context<'a>, mut block: BasicBlock<'a>) -> BasicBlock<'a> {
        match *self {
            // These three kinds of statements just append instructions to the
            // current basic block.
            ast::Statement::Assignment(id, ref expr) => {
                let r = expr.lower(ctx, &mut block);
                block.push(Instruction::Mov(id.into(), r));
                block
            }
            ast::Statement::DerefAssignment(id, ref expr) => {
                let r = expr.lower(ctx, &mut block);
                block.push(Instruction::Deref(id.into(), r));
                block
            }
            ast::Statement::Output(ref expr) => {
                let r = expr.lower(ctx, &mut block);
                block.push(Instruction::Output(r));
                block
            }

            // Lowering `if` statements requires building new basic blocks and
            // finishing the current basic block.
            //
            // When there is an alternative:
            //
            //                  current
            //                  condition
            //        +---------branch-------+
            //        |                      |
            //        V                      V
            //      consequent             alternative
            //      jump                   jump
            //        |                      |
            //        +-----------+   +------+
            //                    |   |
            //                    V   V
            //                  continue
            //
            // When there is no alternative:
            //
            //                  current
            //                  condition
            //           +------branch
            //           |           |
            //           V           |
            //         consequent    |
            //         jump          |
            //           |           |
            //           +-------+   |
            //                   |   |
            //                   V   V
            //                  continue
            ast::Statement::If(ref condition, ref consequent, ref alternative) => {
                let r = condition.lower(ctx, &mut block);

                let mut consequent_block = ctx.new_block();
                for stmt in consequent {
                    consequent_block = stmt.lower(ctx, consequent_block);
                }

                let final_block = ctx.new_block();

                if let Some(ref alternative) = *alternative {
                    let mut alternative_block = ctx.new_block();
                    for stmt in alternative {
                        alternative_block = stmt.lower(ctx, alternative_block);
                    }

                    let alt_block_label = alternative_block.label();
                    ctx.finish_block_with_jump(alternative_block, final_block.label());

                    ctx.finish_block_with_branch(
                        block,
                        r,
                        consequent_block.label(),
                        alt_block_label,
                    );
                } else {
                    ctx.finish_block_with_branch(
                        block,
                        r,
                        consequent_block.label(),
                        final_block.label(),
                    );
                }

                ctx.finish_block_with_jump(consequent_block, final_block.label());

                final_block
            }

            // Lowering `while` statements also requires building new basic
            // blocks and finishing the current basic block.
            //
            //                     current
            //                     jump
            //                       |
            //       +-----------+   |
            //       |           |   |
            //       |           V   V
            //       |          condition
            //       |     +----branch
            //       |     |        |
            //       |     V        |
            //       |    body      |
            //       +----jump      |
            //                      V
            //                   continue
            //
            // If the current block is empty, then we merge it with the
            // condition's block.
            ast::Statement::While(ref condition, ref body) => {
                let mut condition_block = if block.is_empty() {
                    block
                } else {
                    let condition_block = ctx.new_block();
                    ctx.finish_block_with_jump(block, condition_block.label());
                    condition_block
                };

                let mut body_block = ctx.new_block();
                let final_block = ctx.new_block();

                let condition_block_label = condition_block.label();

                let r = condition.lower(ctx, &mut condition_block);
                ctx.finish_block_with_branch(
                    condition_block,
                    r,
                    body_block.label(),
                    final_block.label(),
                );

                for stmt in body {
                    body_block = stmt.lower(ctx, body_block);
                }

                ctx.finish_block_with_jump(body_block, condition_block_label);

                final_block
            }
        }
    }
}

impl<'a, 'b> Lower<'a, 'b> for ast::Function<'a>
where
    'a: 'b,
{
    type Arg = ();
    type Ret = ();

    fn lower(&self, ctx: &mut Context<'a>, _: ()) {
        ctx.register_counter = 0;

        let mut block = ctx.new_block();
        let entry = block.label();

        for stmt in self.body.iter() {
            block = stmt.lower(ctx, block);
        }

        let r = self.ret.lower(ctx, &mut block);
        ctx.finish_block_with_return(block, r);

        debug_assert!(ctx.blocks.iter().all(|b| b.is_some()));
        debug_assert!(!ctx.functions.contains_key(&self.name));

        let num_registers = ctx.register_counter + self.arguments.len() + self.variables.len();
        ctx.functions.insert(self.name, (entry, num_registers));
    }
}

impl<'a, 'b> Lower<'a, 'b> for ast::Program<'a>
where
    'a: 'b,
{
    type Arg = ();
    type Ret = ();

    fn lower(&self, ctx: &mut Context<'a>, _: ()) {
        for f in self.functions.iter() {
            f.lower(ctx, ());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::{self, CanonicalizeIdentifiers, DumpAst};
    use error;
    use parser;
    use typing;
    use typing::constraints::ConstrainTypes;

    #[test]
    fn expression() {
        let expr = ast::Expression::Addition(Box::new([
            ast::Expression::Multiplication(Box::new([
                ast::Expression::Identifier(ast::Identifier("x")),
                ast::Expression::Integer(42),
            ])),
            ast::Expression::Input,
        ]));

        let mut ctx = Context::default();
        let mut block = ctx.new_block();
        expr.lower(&mut ctx, &mut block);

        assert_eq!(
            block.instructions,
            &[
                Instruction::Int(Register::Temp(0), 42),
                Instruction::Mul(
                    Register::Temp(1),
                    Register::Identifier(ast::Identifier("x")),
                    Register::Temp(0)
                ),
                Instruction::Input(Register::Temp(2)),
                Instruction::Add(Register::Temp(3), Register::Temp(1), Register::Temp(2))
            ]
        );
    }

    #[test]
    fn statement() {
        let stmt = ast::Statement::While(
            ast::Expression::Greater(Box::new([
                ast::Expression::Integer(10),
                ast::Expression::Identifier(ast::Identifier("i")),
            ])),
            vec![
                ast::Statement::If(
                    ast::Expression::Greater(Box::new([
                        ast::Expression::Integer(5),
                        ast::Expression::Identifier(ast::Identifier("i")),
                    ])),
                    vec![
                        ast::Statement::Output(
                            ast::Expression::Identifier(ast::Identifier("bottom")),
                        ),
                    ],
                    Some(vec![
                        ast::Statement::Output(ast::Expression::Identifier(ast::Identifier("top"))),
                    ]),
                ),
                ast::Statement::Assignment(
                    ast::Identifier("i"),
                    ast::Expression::Addition(Box::new([
                        ast::Expression::Identifier(ast::Identifier("i")),
                        ast::Expression::Integer(1),
                    ])),
                ),
            ],
        );

        let mut ctx = Context::default();
        let block = ctx.new_block();
        let block = stmt.lower(&mut ctx, block);

        assert!(
            ctx.blocks
                .iter()
                .enumerate()
                .filter(|&(_, b)| b.is_some())
                .all(|(i, b)| i == b.as_ref().unwrap().label().0)
        );

        assert_eq!(ctx.blocks.iter().filter(|b| b.is_none()).count(), 1);
        assert!(ctx.blocks[block.label().0].is_none());

        assert_eq!(
            ctx.blocks,
            &[
                Some(BasicBlock {
                    label: Label(0),
                    instructions: vec![
                        Instruction::Int(Register::Temp(0), 10),
                        Instruction::Gt(
                            Register::Temp(1),
                            Register::Temp(0),
                            Register::Identifier(ast::Identifier("i")),
                        ),
                        Instruction::Branch(Register::Temp(1), Label(1), Label(2)),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(1),
                    instructions: vec![
                        Instruction::Int(Register::Temp(2), 5),
                        Instruction::Gt(
                            Register::Temp(3),
                            Register::Temp(2),
                            Register::Identifier(ast::Identifier("i")),
                        ),
                        Instruction::Branch(Register::Temp(3), Label(3), Label(5)),
                    ],
                }),
                None,
                Some(BasicBlock {
                    label: Label(3),
                    instructions: vec![
                        Instruction::Output(Register::Identifier(ast::Identifier("bottom"))),
                        Instruction::Jump(Label(4)),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(4),
                    instructions: vec![
                        Instruction::Int(Register::Temp(4), 1),
                        Instruction::Add(
                            Register::Temp(5),
                            Register::Identifier(ast::Identifier("i")),
                            Register::Temp(4),
                        ),
                        Instruction::Mov(
                            Register::Identifier(ast::Identifier("i")),
                            Register::Temp(5),
                        ),
                        Instruction::Jump(Label(0)),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(5),
                    instructions: vec![
                        Instruction::Output(Register::Identifier(ast::Identifier("top"))),
                        Instruction::Jump(Label(4)),
                    ],
                })
            ]
        );
    }

    fn lower(source: &'static str) -> error::Result<Context> {
        let mut program = Box::new(
            parser::parse_Program(source).expect("source parses as a program"),
        );

        let functions = HashMap::new();
        let locals = HashMap::new();
        program
            .canonicalize_identifiers(&functions, &locals)
            .unwrap();
        program.dump_ast(0);

        let mut ctx = typing::Context::new();
        let mut constraints = vec![];
        program.constrain_types(&mut ctx, &mut |c| { constraints.push(c); });

        ctx.unify(constraints)?;

        let mut ctx = Context::default();
        program.lower(&mut ctx, ());
        Ok(ctx)
    }

    #[test]
    fn poly_id() {
        let ctx = lower(
            "
poly(x) {
    return x;
}
",
        ).unwrap();

        assert_eq!(
            ctx.blocks,
            &[
                Some(BasicBlock {
                    label: Label(0),
                    instructions: vec![
                        Instruction::Return(Register::Identifier(ast::Identifier("x"))),
                    ],
                })
            ]
        );
    }

    #[test]
    fn poly_deref() {
        let ctx = lower(
            "
poly(x) {
    return *x;
}
    ",
        ).unwrap();

        assert_eq!(
            ctx.blocks,
            &[
                Some(BasicBlock {
                    label: Label(0),
                    instructions: vec![
                        Instruction::Deref(
                            Register::Temp(0),
                            Register::Identifier(ast::Identifier("x")),
                        ),
                        Instruction::Return(Register::Temp(0)),
                    ],
                })
            ]
        );
    }

    #[test]
    fn double() {
        let ctx = lower(
            "
double(x) {
    return x + x;
}
    ",
        ).unwrap();

        assert_eq!(
            ctx.blocks,
            &[
                Some(BasicBlock {
                    label: Label(0),
                    instructions: vec![
                        Instruction::Add(
                            Register::Temp(0),
                            Register::Identifier(ast::Identifier("x")),
                            Register::Identifier(ast::Identifier("x")),
                        ),
                        Instruction::Return(Register::Temp(0)),
                    ],
                })
            ]
        );
    }

    #[test]
    fn recursive_factorial() {
        let ctx = lower(
            "
rec(n) {
    var f;
    if (n==0) { f=1; }
    else { f=n*rec(n-1); }
    return f;
}
",
        ).unwrap();

        assert_eq!(
            ctx.blocks,
            &[
                Some(BasicBlock {
                    label: Label(0),
                    instructions: vec![
                        Instruction::Int(Register::Temp(0), 0),
                        Instruction::Eq(
                            Register::Temp(1),
                            Register::Identifier(ast::Identifier("n")),
                            Register::Temp(0),
                        ),
                        Instruction::Branch(Register::Temp(1), Label(1), Label(3)),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(1),
                    instructions: vec![
                        Instruction::Int(Register::Temp(2), 1),
                        Instruction::Mov(
                            Register::Identifier(ast::Identifier("f")),
                            Register::Temp(2),
                        ),
                        Instruction::Jump(Label(2)),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(2),
                    instructions: vec![
                        Instruction::Return(Register::Identifier(ast::Identifier("f"))),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(3),
                    instructions: vec![
                        Instruction::Int(Register::Temp(3), 1),
                        Instruction::Sub(
                            Register::Temp(4),
                            Register::Identifier(ast::Identifier("n")),
                            Register::Temp(3),
                        ),
                        Instruction::Call(
                            Register::Temp(5),
                            ast::Identifier("rec"),
                            vec![Register::Temp(4)],
                        ),
                        Instruction::Mul(
                            Register::Temp(6),
                            Register::Identifier(ast::Identifier("n")),
                            Register::Temp(5),
                        ),
                        Instruction::Mov(
                            Register::Identifier(ast::Identifier("f")),
                            Register::Temp(6),
                        ),
                        Instruction::Jump(Label(2)),
                    ],
                })
            ]
        )
    }

    #[test]
    fn iterative_factorial() {
        let ctx = lower(
            "
ite(n) {
    var f;
    f = 1;
    while (n>0) {
        f = f*n;
        n = n-1;
    }
    return f;
}
",
        ).unwrap();

        assert_eq!(
            ctx.blocks,
            &[
                Some(BasicBlock {
                    label: Label(0),
                    instructions: vec![
                        Instruction::Int(Register::Temp(0), 1),
                        Instruction::Mov(
                            Register::Identifier(ast::Identifier("f")),
                            Register::Temp(0),
                        ),
                        Instruction::Jump(Label(1)),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(1),
                    instructions: vec![
                        Instruction::Int(Register::Temp(1), 0),
                        Instruction::Gt(
                            Register::Temp(2),
                            Register::Identifier(ast::Identifier("n")),
                            Register::Temp(1),
                        ),
                        Instruction::Branch(Register::Temp(2), Label(2), Label(3)),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(2),
                    instructions: vec![
                        Instruction::Mul(
                            Register::Temp(3),
                            Register::Identifier(ast::Identifier("f")),
                            Register::Identifier(ast::Identifier("n")),
                        ),
                        Instruction::Mov(
                            Register::Identifier(ast::Identifier("f")),
                            Register::Temp(3),
                        ),
                        Instruction::Int(Register::Temp(4), 1),
                        Instruction::Sub(
                            Register::Temp(5),
                            Register::Identifier(ast::Identifier("n")),
                            Register::Temp(4),
                        ),
                        Instruction::Mov(
                            Register::Identifier(ast::Identifier("n")),
                            Register::Temp(5),
                        ),
                        Instruction::Jump(Label(1)),
                    ],
                }),
                Some(BasicBlock {
                    label: Label(3),
                    instructions: vec![
                        Instruction::Return(Register::Identifier(ast::Identifier("f"))),
                    ],
                })
            ]
        );
    }
}
