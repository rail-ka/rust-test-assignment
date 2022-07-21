use std::{
    cell::{Cell, RefCell},
    rc::{Rc, Weak},
};

// round to decimal digits
fn round(x: f32, precision: u32) -> f32 {
    let m = 10i32.pow(precision) as f32;
    (x * m).round() / m
}

/// Value can be computed result of node, static f32 number or input value
#[derive(Debug, Clone)]
enum Value {
    /// computed result of depending node
    Node(Rc<Node>),
    /// static f32 number
    Static(f32),
    /// input value
    Input(Rc<Input>),
}

impl Value {
    /// get f32, if self == Value::Node compute self
    fn get(&self) -> f32 {
        match self {
            Value::Node(node) => node.compute(),
            Value::Static(f) => *f,
            Value::Input(input) => input.val.get(),
        }
    }
}

#[derive(Debug)]
enum Operation {
    Add(Value, Value),
    Mul(Value, Value),
    Sin(Value),
    Pow(Value, Value),
}

impl Operation {
    fn compute(&self) -> f32 {
        match self {
            Operation::Add(value, other) => value.get() + other.get(),
            Operation::Mul(value, rhs) => value.get() * rhs.get(),
            Operation::Sin(val) => val.get().sin(),
            Operation::Pow(value, exponent) => value.get().powf(exponent.get()),
        }
    }
}

#[derive(Debug)]
struct Input {
    val: Cell<f32>,
    /// weak references for depend nodes
    depends: RefCell<Vec<Weak<Node>>>,
}

impl Input {
    fn new(s: &'static str) -> Rc<Input> {
        println!("new input: {s}");
        let input = Input {
            val: Cell::new(f32::NAN),
            depends: RefCell::new(Vec::with_capacity(1)),
        };
        Rc::new(input)
    }

    fn set(&self, val: f32) {
        self.val.set(val);
        for weak in self.depends.borrow().iter() {
            if let Some(node) = weak.upgrade() {
                node.invalidate();
            }
        }
    }
}

#[derive(Debug)]
struct Node {
    /// operation in self node
    op: Operation,
    /// cached value
    cache: Cell<Option<f32>>,
    /// weak references for depend nodes
    depends: RefCell<Vec<Weak<Node>>>,
}

impl Node {
    fn new(op: Operation, depends: &[Value]) -> Rc<Self> {
        let node = Rc::new(Node {
            op,
            cache: Cell::new(None),
            depends: RefCell::new(Vec::with_capacity(1)),
        });
        for n in depends.iter() {
            match n {
                Value::Node(parent) => {
                    parent.depends.borrow_mut().push(Rc::downgrade(&node));
                }
                Value::Input(input) => {
                    input.depends.borrow_mut().push(Rc::downgrade(&node));
                }
                _ => {}
            }
        }
        node
    }

    fn compute(&self) -> f32 {
        match self.cache.get() {
            Some(val) => val,
            None => {
                let val = self.op.compute();
                self.cache.set(Some(val));
                val
            }
        }
    }

    fn invalidate(&self) {
        self.cache.set(None);
        for weak in self.depends.borrow().iter() {
            if let Some(node) = weak.upgrade() {
                node.invalidate();
            }
        }
    }
}

#[test]
fn test_cache() {
    let input = Input::new("x1");
    input.set(3.1);
    let node = pow_f32(Value::Input(input.clone()), Value::Static(2.0));
    assert_eq!(node.cache, Cell::new(None));
    let val = node.compute();
    assert_eq!(node.cache, Cell::new(Some(val)));
    input.set(5.0);
    assert_eq!(node.cache, Cell::new(None));

    let node2 = sin(Value::Node(node));
    let val = node2.compute();
    assert_eq!(node2.cache, Cell::new(Some(val)));
    input.set(3.1);
    assert_eq!(node2.cache, Cell::new(None));
}

fn pow_f32(value: Value, exponent: Value) -> Rc<Node> {
    Node::new(
        Operation::Pow(value.clone(), exponent.clone()),
        &[value, exponent],
    )
}

#[test]
fn test_pow_f32() {
    assert_eq!(
        pow_f32(Value::Static(3.1), Value::Static(2.0)).compute(),
        9.61
    );
}

fn add(value: Value, other: Value) -> Rc<Node> {
    Node::new(
        Operation::Add(value.clone(), other.clone()),
        &[value, other],
    )
}

#[test]
fn test_add() {
    assert_eq!(add(Value::Static(3.2), Value::Static(2.0)).compute(), 5.2);
}

fn sin(value: Value) -> Rc<Node> {
    Node::new(Operation::Sin(value.clone()), &[value])
}

#[test]
fn test_sin() {
    assert_eq!(
        sin(Value::Static(std::f32::consts::FRAC_PI_2)).compute(),
        1.0
    );
}

fn mul(value: Value, rhs: Value) -> Rc<Node> {
    Node::new(Operation::Mul(value.clone(), rhs.clone()), &[value, rhs])
}

#[test]
fn test_mul() {
    assert_eq!(mul(Value::Static(3.2), Value::Static(2.0)).compute(), 6.4);
}

fn main() {
    let x1 = Input::new("x1");
    let x2 = Input::new("x2");
    let x3 = Input::new("x3");

    // y = x1 + x2 * sin(x2 + pow(x3, 3))
    let node4 = pow_f32(Value::Input(x3.clone()), Value::Static(3.0));
    let node3 = add(Value::Input(x2.clone()), Value::Node(node4));
    let node2 = sin(Value::Node(node3));
    let node1 = mul(Value::Input(x2.clone()), Value::Node(node2));
    let graph = add(Value::Input(x1.clone()), Value::Node(node1));

    x1.set(1f32);
    x2.set(2f32);
    x3.set(3f32);

    let mut result = graph.compute();
    result = round(result, 5);
    println!("Graph output = {}", result);
    assert_eq!(round(result, 5), -0.32727);

    x1.set(2f32);
    x2.set(3f32);
    x3.set(4f32);

    result = graph.compute();
    result = round(result, 5);
    println!("Graph output = {}", result);
    assert_eq!(round(result, 5), -0.56656);
}
