//! Values, candidates, tapes and counterexamples, worked out from tests.minimal-values,
//! tests.shrinking and tests.property-verdict, on `SplitMix64`'s draws from known states. The
//! reference interpreter's `interpreter/test/test_props.ml` expects the same values.

use stilt_types::generable::{Graph, Node};

use super::draw::Draws;
use super::shown::shown;
use super::shrink::candidates;
use super::tape;
use super::values::{Val, case, int_word, scalar};

const I64: Node = Node::Int {
    bits: 64,
    signed: true,
};

fn graph(nodes: Vec<Node>, depths: Vec<u32>) -> Graph {
    Graph { nodes, depths }
}

fn word(x: i64) -> Val {
    Val::Word(x.cast_unsigned())
}

#[test]
fn scalars_are_drawn_in_order_at_size_3() {
    let u32 = Node::Int {
        bits: 32,
        signed: false,
    };
    let rows: Vec<Vec<Val>> = (0..6)
        .map(|state| {
            let mut d = Draws::new(state, 0);
            [&I64, &u32, &Node::Str, &Node::Float { f32: true }]
                .into_iter()
                .map(|node| scalar(&mut d, 3, node))
                .collect()
        })
        .collect();
    let s = |t: &str| Val::Str(t.to_owned());
    let expected = vec![
        vec![
            word(7_960_286_522_194_355_700),
            Val::Word(1_917_616_620),
            s("ae\t"),
            Val::Word(0x3f80_8000),
        ],
        vec![word(-3), Val::Word(3), s("H"), Val::Word(0x3f9f_8000)],
        vec![
            word(-3),
            Val::Word(4_293_391_972),
            s("\u{d2586}"),
            Val::Word(0x5887_ccff),
        ],
        vec![
            word(0),
            Val::Word(3),
            s("\u{f25b8}z"),
            Val::Word(0x3ec2_0000),
        ],
        vec![
            word(1),
            Val::Word(653_523_102),
            s("="),
            Val::Word(0x3f16_0000),
        ],
        vec![
            word(2),
            Val::Word(3_657_808_197),
            s("Q"),
            Val::Word(0x9ee9_e9e8),
        ],
    ];
    assert_eq!(rows, expected);
}

#[test]
fn a_draws_low_bits_are_read_as_twos_complement() {
    let draw = |bits, signed| scalar(&mut Draws::new(0, 0), 5, &Node::Int { bits, signed });
    assert_eq!(draw(64, true), word(7_960_286_522_194_355_700));
    assert_eq!(draw(8, false), Val::Word(244));
    assert_eq!(draw(8, true), word(-12));
    assert_eq!(scalar(&mut Draws::new(0, 0), 5, &Node::Bool), Val::Word(1));
}

/// `type Tree = | Leaf | Node(Tree, i64, Tree)`.
fn tree() -> Graph {
    let variants = vec![("Leaf".into(), vec![]), ("Node".into(), vec![0, 1, 0])];
    graph(vec![Node::Variants(variants), I64], vec![1, 0])
}

fn leaf() -> Val {
    Val::Variant(0, Vec::new())
}

fn node(l: Val, x: i64, r: Val) -> Val {
    Val::Variant(1, vec![l, word(x), r])
}

#[test]
fn a_recursive_variant_type_is_generated_within_its_budget() {
    let g = tree();
    let seed = super::seed("|t: Tree| true");
    let cases: Vec<Val> = (0..8).map(|i| case(&g, seed, &[0], i).remove(0)).collect();
    let expected = vec![
        leaf(),
        node(leaf(), 1, leaf()),
        leaf(),
        leaf(),
        node(
            node(leaf(), 3_921_248_834_837_356_098, leaf()),
            7_367_647_082_141_192_896,
            node(leaf(), -1, leaf()),
        ),
        leaf(),
        leaf(),
        node(leaf(), i64::MAX, node(leaf(), 5, leaf())),
    ];
    assert_eq!(cases, expected);
}

fn all(g: &Graph, k: usize, v: &Val) -> Vec<Val> {
    candidates(g, k, v).collect()
}

#[test]
fn candidates_come_in_the_order_of_rule_12() {
    let g = graph(
        vec![
            I64,
            Node::Int {
                bits: 8,
                signed: true,
            },
            Node::Int {
                bits: 8,
                signed: false,
            },
            Node::Float { f32: false },
            Node::Str,
            Node::List(0),
        ],
        vec![0; 6],
    );
    assert_eq!(
        all(&g, 0, &word(-6)),
        [word(0), word(6), word(-3), word(-5)]
    );
    assert_eq!(all(&g, 1, &word(-128)), [word(0), word(-64), word(-127)]);
    assert_eq!(
        all(&g, 2, &Val::Word(5)),
        [Val::Word(0), Val::Word(2), Val::Word(4)]
    );
    let f = |x: f64| Val::Word(x.to_bits());
    assert_eq!(all(&g, 3, &f(-2.5)), [f(0.0), f(2.5), f(-2.0)]);
    assert_eq!(all(&g, 3, &f(3.0)), [f(0.0), f(1.0)]);
    assert_eq!(all(&g, 3, &f(f64::NAN)), [f(0.0)]);
    assert_eq!(all(&g, 3, &f(-0.0)), [f(0.0)]);
    let s = |t: &str| Val::Str(t.to_owned());
    assert_eq!(all(&g, 4, &s("ab")), [s(""), s("b"), s("a"), s("aa")]);
    let list = |xs: &[i64]| Val::Seq(xs.iter().map(|&x| word(x)).collect());
    assert_eq!(
        all(&g, 5, &list(&[1, 0])),
        [list(&[]), list(&[0]), list(&[1]), list(&[0, 0])]
    );
    let t = tree();
    assert_eq!(
        all(&t, 0, &node(node(leaf(), 1, leaf()), 2, leaf())),
        [
            leaf(),
            node(leaf(), 1, leaf()),
            node(leaf(), 2, leaf()),
            node(node(leaf(), 0, leaf()), 2, leaf()),
            node(node(leaf(), 1, leaf()), 0, leaf()),
            node(node(leaf(), 1, leaf()), 1, leaf()),
        ]
    );
}

#[test]
fn a_map_keeps_the_first_key_and_the_last_value_of_equal_keys() {
    let g = graph(vec![Node::Map(1, 2), Node::Str, I64], vec![0; 3]);
    let s = |t: &str| Val::Str(t.to_owned());
    let generated = Val::Map(vec![
        (s("a"), word(1)),
        (s("b"), word(2)),
        (s("A"), word(3)),
    ]);
    let t = tape::write(&g, &[0], std::slice::from_ref(&generated));
    assert_eq!(t.notes(), &[] as &[u64]);
    let settled = tape::settle(&g, &[0], &[generated], &[0, 1, 0]);
    assert_eq!(
        settled,
        [Val::Map(vec![(s("a"), word(3)), (s("b"), word(2))])]
    );
}

#[test]
fn a_counterexample_is_written_by_its_structure() {
    let g = graph(
        vec![
            Node::Record("Point".into(), vec![("x".into(), 1), ("tag".into(), 2)]),
            Node::Float { f32: false },
            Node::Str,
            Node::Tuple(vec![4]),
            Node::Bool,
        ],
        vec![1, 0, 0, 1, 0],
    );
    let point = Val::Seq(vec![
        Val::Word(1.5f64.to_bits()),
        Val::Str("a\"\n".to_owned()),
    ]);
    assert_eq!(shown(&g, 0, &point), "Point { x: 1.5, tag: \"a\\\"\\n\" }");
    assert_eq!(shown(&g, 3, &Val::Seq(vec![Val::Word(0)])), "(false,)");
    assert_eq!(
        shown(
            &tree(),
            0,
            &node(leaf(), int_word(-7, true).cast_signed(), leaf())
        ),
        "Node(Leaf, -7, Leaf)"
    );
}
