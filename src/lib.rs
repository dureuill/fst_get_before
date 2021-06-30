use fst::raw::{Fst, Node, Output};

/// Wraps a Map to add the `get_before` method.
pub struct Map<D> {
    map: fst::Map<D>,
}

impl Map<Vec<u8>> {
    pub fn from_iter(iter: impl Iterator<Item = (u64, u64)>) -> Result<Self, fst::Error> {
        let map = fst::Map::from_iter(iter.map(|(key, value)| (key.to_be_bytes(), value)))?;
        Ok(Self { map })
    }
}

type Backtrack<'a> = Option<(Node<'a>, Output, usize)>;

#[derive(Debug, Clone, Copy)]
struct CompareNext<'a> {
    node: Node<'a>,
    output: Output,
    backtrack: Backtrack<'a>,
    input: &'a [u8],
}

#[derive(Debug, Clone, Copy)]
struct ChooseBiggest<'a> {
    node: Node<'a>,
    output: Output,
}

#[derive(Debug, Clone, Copy)]
enum Outcome<'a> {
    CompareNext(CompareNext<'a>),
    ChooseBiggest(ChooseBiggest<'a>),
    /// Go back to the first byte that is lowest, then ChooseBiggest
    Backtrack(Backtrack<'a>),
    /// Key is lower than every key in the map, abort the search
    Abort,
    /// Reached a final state, output contains the value
    Final(Output),
}

impl<D: AsRef<[u8]>> Map<D> {
    fn backtrack<'a>(raw: &'a Fst<D>, state: Backtrack<'a>) -> Outcome<'a> {
        match state {
            Some((node, output, index)) => {
                let t = node.transition(index);
                let output = output.cat(t.out);
                let next = raw.node(t.addr);
                Outcome::ChooseBiggest(ChooseBiggest { node: next, output })
            }
            None => Outcome::Abort,
        }
    }

    fn choose_biggest<'a>(raw: &'a Fst<D>, state: ChooseBiggest<'a>) -> Outcome<'a> {
        if state.node.len() == 0 {
            return Outcome::Final(state.output.cat(state.node.final_output()));
        }
        let t = state.node.transition(state.node.len() - 1);
        let output = state.output.cat(t.out);
        let next = raw.node(t.addr);
        return Outcome::ChooseBiggest(ChooseBiggest { node: next, output });
    }
    fn compare_next<'a>(raw: &'a Fst<D>, state: CompareNext<'a>) -> Outcome<'a> {
        let input = match state.input.first() {
            Some(&input) => input,
            None => return Outcome::Final(state.output.cat(state.node.final_output())),
        };

        match state.node.find_input(input) {
            None => {
                if state.node.len() == 0 {
                    return Outcome::Abort;
                }
                let mut it = state.node.transitions().enumerate();
                let index = loop {
                    if let Some((index, t)) = it.next() {
                        if t.inp > input {
                            break index;
                        }
                    } else {
                        break state.node.len();
                    }
                };

                if index == 0 {
                    // none is greater than b, either we are equal to t(0), which would have caused find_input to work,
                    // or we are lower than t(0), in which case we should backtrace to the previous byte
                    return Outcome::Backtrack(state.backtrack);
                } else {
                    let t = state.node.transition(index - 1);
                    let output = state.output.cat(t.out);
                    let next = raw.node(t.addr);
                    return Outcome::ChooseBiggest(ChooseBiggest { node: next, output });
                }
            }
            Some(index) => {
                let backtrack = if index == 0 {
                    state.backtrack
                } else {
                    Some((state.node, state.output, index - 1))
                };
                let t = state.node.transition(index);
                let output = state.output.cat(t.out);
                let next = raw.node(t.addr);
                return Outcome::CompareNext(CompareNext {
                    node: next,
                    output,
                    backtrack,
                    input: &state.input[1..],
                });
            }
        }
    }

    /// Returns the value exactly corresponding to the passed key, if it exists.
    pub fn get_exact(&self, key: u64) -> Option<u64> {
        let transition = key.to_be_bytes();
        self.map.get(transition)
    }

    /// Returns the value corresponding to the biggest key that is less or equal to the passed key.
    ///
    /// If no key is less or equal to the passed key, returns `None`.
    pub fn get_before(&self, key: u64) -> Option<u64> {
        let key = key.to_be_bytes();

        let raw = self.map.as_fst();

        let mut outcome = Outcome::CompareNext(CompareNext {
            node: raw.root(),
            output: Output::zero(),
            backtrack: None,
            input: &key,
        });
        loop {
            outcome = match outcome {
                Outcome::CompareNext(state) => Self::compare_next(raw, state),
                Outcome::ChooseBiggest(state) => Self::choose_biggest(raw, state),
                Outcome::Backtrack(state) => Self::backtrack(raw, state),
                Outcome::Final(output) => return Some(output.value()),
                Outcome::Abort => return None,
            }
        }
    }
}

#[cfg(test)]
mod test {

    use super::Map;

    #[test]
    fn test_exact() {
        let map = Map::from_iter(vec![(0, 0), (1, 42), (100, 1000)].into_iter())
            .expect("could not build map");
        assert_eq!(map.get_exact(0), Some(0));
        assert_eq!(map.get_before(0), Some(0));
        assert_eq!(map.get_exact(1), Some(42));
        assert_eq!(map.get_before(1), Some(42));
        assert_eq!(map.get_exact(100), Some(1000));
        assert_eq!(map.get_before(100), Some(1000));
    }

    #[test]
    fn test_before() {
        let map =
            Map::from_iter(vec![(1, 42), (100, 1000)].into_iter()).expect("could not build map");
        assert_eq!(map.get_before(0), None);
        assert_eq!(map.get_before(2), Some(42));
        assert_eq!(map.get_before(110), Some(1000));
    }

    #[test]
    fn test_multiple_bytes() {
        let map = Map::from_iter(vec![(10, 42), (100, 1000), (4444, 28), (70_000, 2074)].into_iter())
            .expect("could not build map");
        assert_eq!(map.get_before(258), Some(1000));
        for i in 0..10 {
            assert_eq!(map.get_before(i), None);
        }
        for  i in 10..100 {
            assert_eq!(map.get_before(i), Some(42));
        }
        for i in 100..4444 {
            assert_eq!(map.get_before(i), Some(1000));
        }
        for i in 4444..70_000 {
            assert_eq!(map.get_before(i), Some(28));
        }
        for i in 70_000..200_000 {
            assert_eq!(map.get_before(i), Some(2074));
        }
    }
}
