use risc_mpc::{Id, Integer, PartyBuilder, Result, Share, TcpChannel, XRegister, U64_BYTES};

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

    let ch = TcpChannel::connect("127.0.0.1:8000")?;
    let mut party = PartyBuilder::new(Id::Party1, ch)
        .register_u64(XRegister::x10, Integer::Public(0x0)) // salaries0 address
        .register_u64(XRegister::x11, Integer::Public(k)) // salaries0 length
        .register_u64(XRegister::x12, Integer::Public(U64_BYTES * k)) // salaries1 address
        .register_u64(XRegister::x13, Integer::Public(n)) // salaries1 length
        .address_range_u64(
            k * U64_BYTES,
            salaries
                .iter()
                .map(|x| Integer::Secret(Share::Arithmetic(*x)))
                .collect(),
        )?
        .build()?;

    party.execute(&program)?;

    let mean = party.register_u64(XRegister::x10)?;

    println!("mean = {mean}");
    Ok(())
}
