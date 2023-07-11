use anyhow::Result;
use wasmparser::{Parser, Payload};

fn print_sizes(wasm: Vec<u8>) -> anyhow::Result<()> {
    let mut type_bytes = 0;
    let mut code_bytes = 0;

    for payload in Parser::new(0).parse_all(&wasm) {
        match payload? {
            Payload::TypeSection(c) => {
                let range = c.range();
                type_bytes = type_bytes + (range.end - range.start);
            },
            Payload::CodeSectionEntry(c) => {
                let range = c.range();
                code_bytes = code_bytes + (range.end - range.start);
            },
            _ => {}
        }
    }

    print!(",{:?},{:?}", code_bytes, type_bytes);
    Ok(())
}

#[derive(clap::Parser)]
pub struct Opts {
    #[clap(flatten)]
    io: wasm_tools::InputOutput,
}

impl Opts {
    pub fn run(&self) -> Result<()> {
        let wasm = self.io.parse_input_wasm()?;
        print_sizes(wasm)?;
        Ok(())
    }
}
