(component
  (type (;0;) (func))
  (type (;1;) (list string))
  (type (;2;) (func (param "x" (type 1))))
  (type (;3;) (record (field "s" string)))
  (type (;4;) (func (param "x" (type 3))))
  (type (;5;) (variant (case "s" string)))
  (type (;6;) (func (param "x" (type 5))))
  (type (;7;) (record (field "s" u32)))
  (type (;8;) (func (param "x" (type 7))))
  (type (;9;) (variant (case "s" u32)))
  (type (;10;) (func (param "x" (type 9))))
  (type (;11;) (list (type 3)))
  (type (;12;) (func (param "x" (type 11))))
  (type (;13;) (list (type 5)))
  (type (;14;) (func (param "x" (type 13))))
  (type (;15;) (list u32))
  (type (;16;) (func (param "x" (type 15))))
  (type (;17;) (func (param "x" u32)))
  (type (;18;) (tuple u32 u32))
  (type (;19;) (func (result (type 18))))
  (type (;20;) (func (result string)))
  (type (;21;) (func (result (type 15))))
  (type (;22;) (func (result u32)))
  (type (;23;) (func (result (type 5))))
  (type (;24;) (list (type 9)))
  (type (;25;) (func (result (type 24))))
  (module (;0;)
    (type (;0;) (func (param i32 i32 i32 i32) (result i32)))
    (type (;1;) (func (param i32 i32 i32)))
    (type (;2;) (func))
    (type (;3;) (func (param i32 i32)))
    (type (;4;) (func (param i32)))
    (type (;5;) (func (result i32)))
    (func (;0;) (type 0) (param i32 i32 i32 i32) (result i32)
      unreachable
    )
    (func (;1;) (type 1) (param i32 i32 i32)
      unreachable
    )
    (func (;2;) (type 2)
      unreachable
    )
    (func (;3;) (type 3) (param i32 i32)
      unreachable
    )
    (func (;4;) (type 3) (param i32 i32)
      unreachable
    )
    (func (;5;) (type 1) (param i32 i32 i32)
      unreachable
    )
    (func (;6;) (type 4) (param i32)
      unreachable
    )
    (func (;7;) (type 3) (param i32 i32)
      unreachable
    )
    (func (;8;) (type 3) (param i32 i32)
      unreachable
    )
    (func (;9;) (type 3) (param i32 i32)
      unreachable
    )
    (func (;10;) (type 3) (param i32 i32)
      unreachable
    )
    (func (;11;) (type 4) (param i32)
      unreachable
    )
    (func (;12;) (type 5) (result i32)
      unreachable
    )
    (func (;13;) (type 5) (result i32)
      unreachable
    )
    (func (;14;) (type 5) (result i32)
      unreachable
    )
    (func (;15;) (type 5) (result i32)
      unreachable
    )
    (func (;16;) (type 5) (result i32)
      unreachable
    )
    (func (;17;) (type 5) (result i32)
      unreachable
    )
    (memory (;0;) 1)
    (export "memory" (memory 0))
    (export "canonical_abi_realloc" (func 0))
    (export "canonical_abi_free" (func 1))
    (export "a" (func 2))
    (export "b" (func 3))
    (export "c" (func 4))
    (export "d" (func 5))
    (export "e" (func 6))
    (export "f" (func 7))
    (export "g" (func 8))
    (export "h" (func 9))
    (export "i" (func 10))
    (export "j" (func 11))
    (export "k" (func 12))
    (export "l" (func 13))
    (export "m" (func 14))
    (export "n" (func 15))
    (export "o" (func 16))
    (export "p" (func 17))
  )
  (instance (;0;) (instantiate (module 0)))
  (alias export (instance 0) "a" (func (;0;)))
  (alias export (instance 0) "b" (func (;1;)))
  (alias export (instance 0) "c" (func (;2;)))
  (alias export (instance 0) "d" (func (;3;)))
  (alias export (instance 0) "e" (func (;4;)))
  (alias export (instance 0) "f" (func (;5;)))
  (alias export (instance 0) "g" (func (;6;)))
  (alias export (instance 0) "h" (func (;7;)))
  (alias export (instance 0) "i" (func (;8;)))
  (alias export (instance 0) "j" (func (;9;)))
  (alias export (instance 0) "k" (func (;10;)))
  (alias export (instance 0) "l" (func (;11;)))
  (alias export (instance 0) "m" (func (;12;)))
  (alias export (instance 0) "n" (func (;13;)))
  (alias export (instance 0) "o" (func (;14;)))
  (alias export (instance 0) "p" (func (;15;)))
  (func (;16;) (canon.lift (type 0) (func 0)))
  (func (;17;) (canon.lift (type 2) utf8 (into (instance 0)) (func 1)))
  (func (;18;) (canon.lift (type 4) utf8 (into (instance 0)) (func 2)))
  (func (;19;) (canon.lift (type 6) utf8 (into (instance 0)) (func 3)))
  (func (;20;) (canon.lift (type 8) (func 4)))
  (func (;21;) (canon.lift (type 10) (func 5)))
  (func (;22;) (canon.lift (type 12) utf8 (into (instance 0)) (func 6)))
  (func (;23;) (canon.lift (type 14) utf8 (into (instance 0)) (func 7)))
  (func (;24;) (canon.lift (type 16) (into (instance 0)) (func 8)))
  (func (;25;) (canon.lift (type 17) (func 9)))
  (func (;26;) (canon.lift (type 19) (func 10)))
  (func (;27;) (canon.lift (type 20) utf8 (into (instance 0)) (func 11)))
  (func (;28;) (canon.lift (type 21) (into (instance 0)) (func 12)))
  (func (;29;) (canon.lift (type 22) (func 13)))
  (func (;30;) (canon.lift (type 23) utf8 (into (instance 0)) (func 14)))
  (func (;31;) (canon.lift (type 25) (into (instance 0)) (func 15)))
  (export "r" (type 3))
  (export "v" (type 5))
  (export "r-no-string" (type 7))
  (export "v-no-string" (type 9))
  (export "a" (func 16))
  (export "b" (func 17))
  (export "c" (func 18))
  (export "d" (func 19))
  (export "e" (func 20))
  (export "f" (func 21))
  (export "g" (func 22))
  (export "h" (func 23))
  (export "i" (func 24))
  (export "j" (func 25))
  (export "k" (func 26))
  (export "l" (func 27))
  (export "m" (func 28))
  (export "n" (func 29))
  (export "o" (func 30))
  (export "p" (func 31))
)