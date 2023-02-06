use wasmparser::*;

#[test]
fn name_annotations() -> anyhow::Result<()> {
    assert_module_name("foo", r#"(module $foo)"#)?;
    assert_module_name("foo", r#"(module (@name "foo"))"#)?;
    assert_module_name("foo", r#"(module $bar (@name "foo"))"#)?;
    assert_module_name("foo bar", r#"(module $bar (@name "foo bar"))"#)?;
    Ok(())
}

fn assert_module_name(expected_name: &str, wat: &str) -> anyhow::Result<()> {
    let wasm = wat::parse_str(wat)?;
    let mut found = false;
    for s in get_name_section(&wasm)? {
        match s? {
            Name::Module { name, .. } => {
                assert_eq!(name, expected_name);
                found = true;
            }
            _ => {}
        }
    }
    assert!(found);
    Ok(())
}

#[test]
fn func_annotations() -> anyhow::Result<()> {
    assert_func_name("foo", r#"(module (func $foo))"#)?;
    assert_func_name("foo", r#"(module (func (@name "foo")))"#)?;
    assert_func_name("foo", r#"(module (func $bar (@name "foo")))"#)?;
    assert_func_name("foo bar", r#"(module (func $bar (@name "foo bar")))"#)?;
    Ok(())
}

fn assert_func_name(name: &str, wat: &str) -> anyhow::Result<()> {
    let wasm = wat::parse_str(wat)?;
    let mut found = false;
    for s in get_name_section(&wasm)? {
        match s? {
            Name::Function(n) => {
                let naming = n.into_iter().next().unwrap()?;
                assert_eq!(naming.index, 0);
                assert_eq!(naming.name, name);
                found = true;
            }
            _ => {}
        }
    }
    assert!(found);
    Ok(())
}

#[test]
fn precheck_annotations() -> anyhow::Result<()> {
    //let str = wat::parse_str(r#"(module (func (param $a i32) (result $b i32) (post (eq $a $b))))"#)?;
    //inspect_types(r#"(module (func (param $a i32) (result $b i32) (post (eq $a $b))))"#)?;
    //wasmparser::
    //wat::parse_str(r#"(module (func (param i32 i32) (result $b i32) (post (eq (i32 1) (i32.gt_s $b (i32 0))))))"#)?;
    //wat::parse_str(r#"(module (func (param (@name "foo") i32)))"#)?;

    let wasm = wat::parse_str(r#"(module
        (func
            (param $a i32)
            (result $b i32)
            (post (eq $b (i32.add (i32 1) $a)))
            (local.get 0)
            (i32.const 1)
            i32.add
        )
        (func
            (result $b i32)
            (post (eq (i32 1) (i32.gt_s $b (i32 0))))
            (i32.const 42)
            (call 0)
        )
    )"#)?;

    wasmparser::validate(&wasm.as_slice())?;
    Ok(())
}

// [0, 97, 115, 109, 1, 0, 0, 0, 1, 6, 1, 96, 1, 127, 1, 127, 3, 2, 1, 0, 10, 4, 1, 2, 0, 11, 0, 13, 4, 110, 97, 109, 101, 2, 6, 1, 0, 1, 0, 1, 97]
// [0, 97, 115, 109, 1, 0, 0, 0, 1, 13, 1, 96, 1, 127, 1, 127, 0, 1, 1, 33, 0, 34, 0, 3, 2, 1, 0, 10, 4, 1, 2, 0, 11, 0, 13, 4, 110, 97, 109, 101, 2, 6, 1, 0, 1, 0, 1, 97]

#[test]
fn precheck_block_annotations() -> anyhow::Result<()> {
    //wat::parse_str(r#"(module (func block (param $a i32) (pre (eq $a (i32 0))) drop end))"#)?;
    /*wat::parse_str(
        r#"(module (func (param $a i32) block (param $a i32) (pre (eq $a (local $a))) drop end))"#,
    )?;*/
    //wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (pre (eq $a (local $a))) drop end))"#)?;
    //wat::parse_str(r#"(module (func (param $l i32) (i32.const 1) block (param $a i32) (pre (eq $a (i32 0))) (post (eq (local $l) (i32.add $a (i32 1)))) (i32.const 1) i32.add (local.set $l) end))"#)?;
    //let wasm = wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (result $b i32) (pre (eq $a (i32 0))) (post (eq $b (i32.add $a (i32 1)))) (i32.const 1) i32.add end drop))"#)?;
    // Expect fail
    //let wasm = wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (result $b i32) (pre (eq $a (i32 0))) (post (eq $b (i32.add $a (i32 1)))) (i32.const 2) i32.add end drop))"#)?;
    //let wasm = wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (result $b i32) (pre (eq $a (i32 0))) (post (eq $b (i32.add $a (i32 1)))) (i32.const 1) (br 0) i32.add end drop))"#)?;
    // Expect fail
    //let wasm = wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (result $b i32) (pre (eq $a (i32 0))) (post (eq $b (i32.add $a (i32 1)))) (i32.const 2) (br 0) i32.add end drop))"#)?;
    //let wasm = wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (result $b i32) (pre (eq $a (i32 0))) (post (eq $b (i32.add $a (i32 1)))) (i32.const 1) i32.add (i32.const 1) (br_if 0) end drop))"#)?;
    // Expect fail
    //let wasm = wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (result $b i32) (pre (eq $a (i32 0))) (post (eq $b (i32.add $a (i32 1)))) (i32.const 2) i32.add (i32.const 0) (br_if 0) end drop))"#)?;
    // Expect fail
    //let wasm = wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (result $b i32) (pre (eq $a (i32 0))) (post (eq $b (i32.add $a (i32 1)))) (i32.const 2) i32.add (i32.const 1) (br_if 0) unreachable end drop))"#)?;
    // Expect fail
    //let wasm = wat::parse_str(r#"(module (func (i32.const 0) block (param $a i32) (result $b i32) (pre (eq $a (i32 0))) (post (eq $b (i32.add $a (i32 1)))) (i32.const 2) i32.add (i32.const 1) (br_if 0) end drop))"#)?;
    // Function definitions cannot reference locals
    //wat::parse_str(r#"(module (func (param $a i32) (pre (eq $a (local $b)))))"#)?;
    // Not sure this is legal anyway but disallowed
    //wat::parse_str(r#"(module (type (func (param $a i32) (pre (eq $a (local $b))))) (func (param $b i32) block (type 0) drop end))"#)?;

    //wasmparser::validate(&wasm.as_slice())?;
    Ok(())
}

#[test]
fn precheck_instructions() -> anyhow::Result<()> {
    let wasm = wat::parse_str(r#"(module (func (local i32) (local i32) (local.get 0) (local.get 1) (local.get 1) (i32.const 1) select i32.div_s drop))"#)?;
    wasmparser::validate(&wasm.as_slice())?;
    Ok(())
}

#[test]
fn local_annotations() -> anyhow::Result<()> {
    assert_local_name("foo", r#"(module (func (param $foo i32)))"#)?;
    assert_local_name("foo", r#"(module (func (local $foo i32)))"#)?;
    assert_local_name("foo", r#"(module (func (param (@name "foo") i32)))"#)?;
    assert_local_name("foo", r#"(module (func (local (@name "foo") i32)))"#)?;
    assert_local_name("foo", r#"(module (func (param $bar (@name "foo") i32)))"#)?;
    //assert_local_name("foo", r#"(module (func ((((i32 a)) ()) -> ((i32 b) (= a b)))))"#)?;
    assert_local_name("foo", r#"(module (func (local $bar (@name "foo") i32)))"#)?;
    assert_local_name(
        "foo bar",
        r#"(module (func (param $bar (@name "foo bar") i32)))"#,
    )?;
    assert_local_name(
        "foo bar",
        r#"(module (func (local $bar (@name "foo bar") i32)))"#,
    )?;
    Ok(())
}

fn assert_local_name(name: &str, wat: &str) -> anyhow::Result<()> {
    let wasm = wat::parse_str(wat)?;
    let mut found = false;
    for s in get_name_section(&wasm)? {
        match s? {
            Name::Local(n) => {
                let naming = n
                    .into_iter()
                    .next()
                    .unwrap()?
                    .names
                    .into_iter()
                    .next()
                    .unwrap()?;
                assert_eq!(naming.index, 0);
                assert_eq!(naming.name, name);
                found = true;
            }
            _ => {}
        }
    }
    assert!(found);
    Ok(())
}

fn get_name_section(wasm: &[u8]) -> anyhow::Result<NameSectionReader<'_>> {
    for payload in Parser::new(0).parse_all(&wasm) {
        if let Payload::CustomSection(c) = payload? {
            if c.name() == "name" {
                return Ok(NameSectionReader::new(c.data(), c.data_offset())?);
            }
        }
    }
    panic!("no name section found");
}

fn inspect_types(wat: &str) -> anyhow::Result<()> {
    let wasm = wat::parse_str(wat)?;
    //wasmparser::validate(&wasm.as_slice())?;
    for _ in get_type_section(&wasm)? {
        // Just exercising the reader
    }
    Ok(())
}

fn get_type_section(wasm: &[u8]) -> anyhow::Result<TypeSectionReader<'_>> {
    for payload in Parser::new(0).parse_all(&wasm) {
        if let Payload::TypeSection(c) = payload? {
            return Ok(c);
        }
    }
    panic!("no name section found");
}

#[test]
fn custom_section_order() -> anyhow::Result<()> {
    let bytes = wat::parse_str(
        r#"
            (module
              (@custom "A" "aaa")
              (type (func))
              (@custom "B" (after func) "bbb")
              (@custom "C" (before func) "ccc")
              (@custom "D" (after last) "ddd")
              (table 10 funcref)
              (func (type 0))
              (@custom "E" (after import) "eee")
              (@custom "F" (before type) "fff")
              (@custom "G" (after data) "ggg")
              (@custom "H" (after code) "hhh")
              (@custom "I" (after func) "iii")
              (@custom "J" (before func) "jjj")
              (@custom "K" (before first) "kkk")
            )
        "#,
    )?;
    macro_rules! assert_matches {
        ($a:expr, $b:pat $(if $cond:expr)? $(,)?) => {
            match &$a {
                $b $(if $cond)? => {}
                a => panic!("`{:?}` doesn't match `{}`", a, stringify!($b)),
            }
        };
    }
    let wasm = Parser::new(0)
        .parse_all(&bytes)
        .collect::<Result<Vec<_>>>()?;
    assert_matches!(wasm[0], Payload::Version { .. });
    assert_matches!(
        wasm[1],
        Payload::CustomSection(c) if c.name() == "K"
    );
    assert_matches!(
        wasm[2],
        Payload::CustomSection(c) if c.name() == "F"
    );
    assert_matches!(wasm[3], Payload::TypeSection(_));
    assert_matches!(
        wasm[4],
        Payload::CustomSection(c) if c.name() == "E"
    );
    assert_matches!(
        wasm[5],
        Payload::CustomSection(c) if c.name() == "C"
    );
    assert_matches!(
        wasm[6],
        Payload::CustomSection(c) if c.name() == "J"
    );
    assert_matches!(wasm[7], Payload::FunctionSection(_));
    assert_matches!(
        wasm[8],
        Payload::CustomSection(c) if c.name() == "B"
    );
    assert_matches!(
        wasm[9],
        Payload::CustomSection(c) if c.name() == "I"
    );
    assert_matches!(wasm[10], Payload::TableSection(_));
    assert_matches!(wasm[11], Payload::CodeSectionStart { .. });
    assert_matches!(wasm[12], Payload::CodeSectionEntry { .. });
    assert_matches!(
        wasm[13],
        Payload::CustomSection(c) if c.name() == "H"
    );
    assert_matches!(
        wasm[14],
        Payload::CustomSection(c) if c.name() == "G"
    );
    assert_matches!(
        wasm[15],
        Payload::CustomSection(c) if c.name() == "A"
    );
    assert_matches!(
        wasm[16],
        Payload::CustomSection(c) if c.name() == "D"
    );

    match &wasm[17] {
        Payload::End(x) if *x == bytes.len() => {}
        p => panic!("`{:?}` doesn't match expected length of {}", p, bytes.len()),
    }

    Ok(())
}
