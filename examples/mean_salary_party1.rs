use risc_mpc::{PartyBuilder, Register, Result, Share, TcpChannel, Value, PARTY_1, U64_BYTES};

fn main() -> Result<()> {
    env_logger::init();

    // https://godbolt.org/z/nGWWb5bbn
    let program = "
        mean:
                addi    sp, sp, -16
                sd      ra, 8(sp)
                li      a6, 0
                slli    a5, a1, 3
                beqz    a5, .LBB0_2
        .LBB0_1:
                ld      a4, 0(a0)
                addi    a0, a0, 8
                add     a6, a6, a4
                addi    a5, a5, -8
                bnez    a5, .LBB0_1
        .LBB0_2:
                slli    a0, a3, 3
                beqz    a0, .LBB0_4
        .LBB0_3:
                ld      a4, 0(a2)
                addi    a2, a2, 8
                add     a6, a6, a4
                addi    a0, a0, -8
                bnez    a0, .LBB0_3
        .LBB0_4:
                add     a1, a1, a3
                beqz    a1, .LBB0_6
                divu    a0, a6, a1
                ld      ra, 8(sp)
                addi    sp, sp, 16
                ret
        .LBB0_6:
    "
    .parse()?;

    let salaries = [1200, 3500, 900, 4000, 1750, 1000];
    let k = salaries.len() as u64;
    let n = k;

    let ch = TcpChannel::new(PARTY_1, "127.0.0.1:8000".parse().unwrap())?;
    let mut party = PartyBuilder::new(PARTY_1, ch)
        .register(Register::x10, Value::Public(0x0)) // salaries0 address
        .register(Register::x11, Value::Public(k)) // salaries0 length
        .register(Register::x12, Value::Public(U64_BYTES * k)) // salaries1 address
        .register(Register::x13, Value::Public(n)) // salaries1 length
        .address_range(
            k * U64_BYTES,
            salaries
                .iter()
                .map(|x| Value::Secret(Share::Arithmetic(*x)))
                .collect(),
        )?
        .build()?;

    party.execute(&program)?;

    let mean = party.register(Register::x10)?;

    println!("mean = {mean}");
    Ok(())
}
