(module
  (memory 1)
  (func (export "load_from_known_offset") (result i32)
    i32.const 100
    i32.const 4
    i32.add
    i32.load))
