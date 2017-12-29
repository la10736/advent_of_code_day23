#![feature(conservative_impl_trait)]
#![feature(iterator_step_by)]

extern crate primal;

use std::io::prelude::*;

fn read_all<S: AsRef<std::path::Path>>(path: S) -> String {
    let mut content = String::new();
    let mut f = std::fs::File::open(path).unwrap();
    f.read_to_string(&mut content).unwrap();
    content
}

fn count_no_prime(f: i32, to: i32) -> i32 {
    let mut count = 0;
    for n in (f..(to + 1)).step_by(17) {
        if !primal::is_prime(n as u64) {
            count += 1;
        }
    }
    count
}

fn main() {
    let fname = std::env::args().nth(1).unwrap_or(String::from("example"));
    let content = read_all(fname);

    let mut program = Program::new(Default::default(), compile(&content));
    for s in 0..10 {
        program.code[2] = Sub('c', Val(-17 * s));
        program.cpu.reset();
        let cnt = (&mut program).filter(|&cmd|
            match cmd {
                Mul(_, _) => true,
                _ => false
            }
        ).count();

        println!("Result {}", cnt);
        let res = count_no_prime(99, 100 + (17 * s));
        println!("c-b {} => {} -> {}  ===> [{}]", (s * 17), s, program.cpu.reg('h'), res);
    }

    program.cpu.reset();
    program.cpu.reg_set('a', 1);
    (&mut program).take(10).count();

    let b = program.cpu.reg('b');
    let c = program.cpu.reg('c');
    program.cpu.dump_registers();
    let res = count_no_prime(b, c);

    println!("Solution Second half = {}", res);
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum Resolv {
    Val(i32),
    Reg(char),
}

impl<S: AsRef<str>> From<S> for Resolv {
    fn from(l: S) -> Self {
        let l = l.as_ref();
        match l.parse::<i32>() {
            Ok(v) => Val(v),
            _ => Reg(l.chars().nth(0).unwrap())
        }
    }
}


#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum Command {
    Set(char, Resolv),
    Sub(char, Resolv),
    Mul(char, Resolv),
    Jnz(Resolv, Resolv),
}

impl<S: AsRef<str>> From<S> for Command {
    fn from(l: S) -> Self {
        let l = l.as_ref();
        let cmd = &l[..3];
        let tokens = l[4..].splitn(2, ' ').collect::<Vec<_>>();
        let reg = tokens[0].chars().nth(0).unwrap();
        let resolv = Resolv::from(tokens[1]);
        match cmd {
            "set" => Set(reg, resolv),
            "sub" => Sub(reg, resolv),
            "mul" => Mul(reg, resolv),
            "jnz" => Jnz(tokens[0].into(), resolv),
            _ => panic!("Comando non conosciuto")
        }
    }
}

use Command::*;
use Resolv::*;

fn compile<S: AsRef<str>>(code: S) -> Vec<Command> {
    code.as_ref().lines().map(|l| l.into()).collect()
}

struct Cpu {
    registers: std::collections::HashMap<char, i32>,
    pc: i32,
}

impl Default for Cpu {
    fn default() -> Self {
        Self {
            registers: Cpu::default_registers(),
            pc: 0,
        }
    }
}

impl Cpu {
    fn reg_set(&mut self, r: char, v: i32) {
        self.registers.insert(r, v);
    }

    fn exec(&mut self, cmd: Command) {
        match cmd {
            Set(r, res) => {
                let val = self.resolve(res);
                self.registers.insert(r, val);
            }
            Sub(r, res) => {
                let val = self.registers[&r] - self.resolve(res);
                self.registers.insert(r, val);
            }
            Mul(r, res) => {
                let val = self.registers[&r] * self.resolve(res);
                self.registers.insert(r, val);
            }
            Jnz(cond, amount) => {
                if self.resolve(cond) != 0 {
                    self.pc += self.resolve(amount) - 1;
                }
            }
        }
        self.pc += 1;
    }

    fn resolve(&self, res: Resolv) -> i32 {
        match res {
            Val(v) => v,
            Reg(r) => self.reg(r)
        }
    }

    fn reg(&self, r: char) -> i32 {
        self.registers[&r]
    }

    fn reset(&mut self) {
        self.registers = Self::default_registers();
        self.pc = 0;
    }

    fn default_registers() -> std::collections::HashMap<char, i32> {
        "abcdefgh".chars().map(|c| (c, 0)).collect()
    }

    fn registers_name(&self) -> impl Iterator<Item=char> {
        "abcdefgh".chars()
    }

    fn dump_registers(&self) {
        self.registers_name().for_each(|r|
            print!(" {} = {:7} ", r, self.registers[&r])
        );
        println!()
    }
}

struct Program {
    cpu: Cpu,
    code: Vec<Command>,
}

impl Program {
    fn new(cpu: Cpu, code: Vec<Command>) -> Self {
        Self { cpu, code }
    }

    fn valid_pc(&self) -> bool {
        self.cpu.pc >= 0 && (self.cpu.pc as usize) < self.code.len()
    }
}

impl Iterator for Program {
    type Item = Command;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.valid_pc() {
            return None;
        }

        assert!(self.cpu.pc >= 0);
        let command = self.code[self.cpu.pc as usize];
        self.cpu.exec(command);

        Some(command)
    }
}


#[cfg(test)]
mod test {
    use super::*;

    static CODE: &'static str = "\
    set a 10\n\
    set b c\n\
    sub a -3\n\
    sub d b\n\
    mul a 1\n\
    mul a b\n\
    jnz 10 20\n\
    jnz a b\
    ";

    #[test]
    fn parse_line() {
        assert_eq!(Sub('a', Val(-3)), Command::from("sub a -3"));
        assert_eq!(Sub('a', Reg('b')), Command::from("sub a b"));
        assert_eq!(Jnz(Val(10), Val(20)), Command::from("jnz 10 20"));
    }

    #[test]
    fn parser() {
        assert_eq!(vec![
            Set('a', Val(10)),
            Set('b', Reg('c')),
            Sub('a', Val(-3)),
            Sub('d', Reg('b')),
            Mul('a', Val(1)),
            Mul('a', Reg('b')),
            Jnz(Val(10), Val(20)),
            Jnz(Reg('a'), Reg('b')),
        ], compile(CODE));
    }

    #[test]
    fn cpu_exec() {
        let mut cpu = Cpu::default();

        assert_eq!(0, cpu.reg('a'));

        cpu.exec(Set('a', Val(10)));

        assert_eq!(10, cpu.reg('a'));
    }

    #[test]
    fn cpu_exec_two_resolve() {
        let mut cpu = Cpu::default();


        cpu.exec(Set('a', Val(10)));
        cpu.exec(Set('b', Val(3)));

        cpu.exec(Mul('b', Reg('a')));

        assert_eq!(30, cpu.reg('b'));
    }

    #[test]
    fn cpu_program_counter() {
        let mut cpu = Cpu::default();

        assert_eq!(0, cpu.pc);

        // Step forward
        cpu.exec(Set('a', Val(10)));

        assert_eq!(1, cpu.pc);

        // Jump
        cpu.exec(Jnz(Val(1), Val(3)));

        assert_eq!(4, cpu.pc);

        // Backward
        cpu.exec(Jnz(Val(1), Val(-1)));

        assert_eq!(3, cpu.pc);
    }

    #[test]
    fn iterate_over_a_program_should_emit_processed_command() {
        let cpu = Cpu::default();

        let mut program = Program::new(cpu, compile(CODE));

        assert_eq!(Set('a', Val(10)), program.next().unwrap());
        assert_eq!(Set('b', Reg('c')), program.next().unwrap())
    }

    #[test]
    fn end_of_program_reached() {
        let mut program = Program::new(Default::default(),
                                       vec![Set('a', Val(12))]);
        program.next();

        assert!(program.next().is_none());
    }

    #[test]
    fn out_of_code() {
        let mut program = Program::new(Default::default(),
                                       vec![Jnz(Val(1), Val(-5))]);
        program.next();

        assert!(program.next().is_none());
    }
}
