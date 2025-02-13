use risc_mpc::{
    Id, Integer, PartyBuilder, Result, Share, TcpChannel, XRegister, A2B_AND_TRIPLES, U64_BYTES,
};
use std::collections::BTreeSet;

fn main() -> Result<()> {
    env_logger::init();

    // https://godbolt.org/z/zjcPTzr8W
    let program = "
        psi:
                li      a6, 0
                li      a7, 0
                li      t1, 0
        .LBB0_1:
                slli    t0, a7, 3
                add     t0, t0, a2
                slli    t2, t1, 3
                add     t2, t2, a0
        .LBB0_2:
                sltu    t3, a7, a3
                sltu    a5, t1, a1
                and     a5, a5, t3
                beqz    a5, .LBB0_8
                ld      t3, 0(t2)
                ld      a5, 0(t0)
                bgeu    t3, a5, .LBB0_5
                addi    t1, t1, 1
                addi    t2, t2, 8
                j       .LBB0_2
        .LBB0_5:
                bgeu    a5, t3, .LBB0_7
                addi    a7, a7, 1
                j       .LBB0_1
        .LBB0_7:
                addi    t1, t1, 1
                addi    a7, a7, 1
                slli    a5, a6, 3
                add     a5, a5, a4
                sd      t3, 0(a5)
                addi    a6, a6, 1
                j       .LBB0_1
        .LBB0_8:
                mv      a0, a6
                ret
    "
    .parse()?;

    let set = BTreeSet::from([1, 2, 3]);
    let n = set.len() as u64;
    let k = n;

    let ch = TcpChannel::bind("127.0.0.1:8000")?;
    let mut party = PartyBuilder::new(Id::Party0, ch)
        .register_u64(XRegister::x10, Integer::Public(0x0)) // set0 address
        .register_u64(XRegister::x11, Integer::Public(n)) // set0 length
        .register_u64(XRegister::x12, Integer::Public(U64_BYTES * n)) // set1 address
        .register_u64(XRegister::x13, Integer::Public(k)) // set1 length
        .register_u64(XRegister::x14, Integer::Public(U64_BYTES * (n + k))) // intersection address
        .address_range_u64(
            0x0,
            set.iter()
                .map(|x| Integer::Secret(Share::Arithmetic(*x)))
                .collect(),
        )?
        .n_and_triples(A2B_AND_TRIPLES * 2 * (n + k)) // 2 lt per set element cmp
        .build()?;

    party.execute(&program)?;

    let len = party.register_u64(XRegister::x10)?;
    let intersection =
        party.address_range_u64(U64_BYTES * (n + k)..U64_BYTES * (n + k) + U64_BYTES * len)?;

    println!("intersection = {intersection:?}");
    Ok(())
}
