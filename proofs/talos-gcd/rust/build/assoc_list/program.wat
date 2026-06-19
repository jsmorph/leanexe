(module
  (type (;0;) (func (param i64 i64) (result i64)))
  (type (;1;) (func (result i64)))
  (type (;2;) (func (param i64) (result i64)))
  (type (;3;) (func (param i64 i64) (result i64)))
  (type (;4;) (func (param i64) (result i64)))
  (type (;5;) (func))
  (type (;6;) (func (param i64) (result i64)))
  (type (;7;) (func (param i64)))
  (memory (;0;) 16)
  (global (;0;) (mut i64) i64.const 4096)
  (global (;1;) (mut i64) i64.const 0)
  (global (;2;) (mut i64) i64.const 0)
  (global (;3;) (mut i64) i64.const 0)
  (global (;4;) (mut i64) i64.const 0)
  (global (;5;) (mut i64) i64.const 0)
  (export "memory" (memory 0))
  (export "lookupDemo" (func 2))
  (export "alloc" (func 4))
  (export "reset" (func 5))
  (export "retain" (func 6))
  (export "release" (func 7))
  (export "free" (func 7))
  (func (;0;) (type 0) (param i64 i64) (result i64)
    (local i64 i64 i64 i64 i64 i64)
    local.get 0
    local.set 2
    local.get 2
    local.set 7
    local.get 7
    i64.const 0
    i64.add
    i32.wrap_i64
    i64.load
    i64.const 0
    i64.eq
    if ;; label = @1
      i64.const 0
      local.set 6
    else
      local.get 2
      local.set 7
      local.get 7
      i64.const 8
      i64.add
      i32.wrap_i64
      i64.load
      local.get 1
      i64.eq
      if (result i64) ;; label = @2
        i64.const 1
      else
        i64.const 0
      end
      i64.const 1
      i64.eq
      if (result i64) ;; label = @2
        i64.const 1
      else
        i64.const 0
      end
      i64.const 0
      i64.eq
      i32.eqz
      if ;; label = @2
        local.get 2
        local.set 7
        local.get 7
        i64.const 16
        i64.add
        i32.wrap_i64
        i64.load
        local.set 6
      else
        local.get 2
        local.set 7
        local.get 7
        i64.const 24
        i64.add
        i32.wrap_i64
        i64.load
        local.set 3
        local.get 1
        local.set 4
        local.get 3
        local.get 4
        call 0
        local.set 5
        local.get 5
        local.set 6
      end
    end
    local.get 6
  )
  (func (;1;) (type 1) (result i64)
    (local i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64 i64)
    i64.const 1
    local.set 2
    i64.const 7
    local.set 3
    i64.const 70
    local.set 4
    i64.const 1
    local.set 9
    i64.const 2
    local.set 10
    i64.const 20
    local.set 11
    i64.const 1
    local.set 16
    i64.const 9
    local.set 17
    i64.const 90
    local.set 18
    i64.const 1
    local.set 23
    i64.const 2
    local.set 24
    i64.const 22
    local.set 25
    i64.const 0
    local.set 30
    i64.const 0
    local.set 31
    i64.const 0
    local.set 32
    i64.const 0
    local.set 33
    i64.const 32
    i64.const 7
    i64.add
    i64.const 8
    i64.div_u
    i64.const 8
    i64.mul
    local.set 36
    local.get 36
    i64.const 8
    i64.lt_u
    if ;; label = @1
      i64.const 8
      local.set 36
    end
    i64.const 0
    local.set 41
    i64.const 0
    local.set 37
    global.get 1
    local.set 38
    block ;; label = @1
      loop ;; label = @2
        local.get 38
        i64.const 0
        i64.eq
        br_if 1 (;@1;)
        local.get 41
        i64.const 0
        i64.ne
        br_if 1 (;@1;)
        local.get 38
        i64.const 32
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 39
        local.get 38
        i64.const 8
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 40
        local.get 39
        local.get 36
        i64.ge_u
        if ;; label = @3
          local.get 37
          i64.const 0
          i64.eq
          if ;; label = @4
            local.get 40
            global.set 1
          else
            local.get 37
            i64.const 8
            i64.sub
            i32.wrap_i64
            local.get 40
            i64.store
          end
          local.get 38
          i64.const 48
          i64.sub
          i32.wrap_i64
          i64.const 5501223100278326855
          i64.store
          local.get 38
          i64.const 40
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 38
          i64.const 32
          i64.sub
          i32.wrap_i64
          local.get 39
          i64.store
          local.get 38
          i64.const 24
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 38
          i64.const 16
          i64.sub
          i32.wrap_i64
          i64.const 4
          i64.store
          local.get 38
          i64.const 8
          i64.sub
          i32.wrap_i64
          i64.const 8
          i64.store
          local.get 38
          local.set 41
        else
          local.get 38
          local.set 37
          local.get 40
          local.set 38
        end
        br 0 (;@2;)
      end
    end
    local.get 41
    i64.const 0
    i64.eq
    if ;; label = @1
      global.get 0
      i64.const 48
      i64.add
      local.get 36
      i64.add
      local.tee 39
      global.get 0
      i64.lt_u
      if ;; label = @2
        unreachable
      end
      local.get 39
      i64.const 1
      i64.sub
      i64.const 65536
      i64.div_u
      i64.const 1
      i64.add
      local.set 40
      memory.size
      i64.extend_i32_u
      local.get 40
      i64.lt_u
      if ;; label = @2
        local.get 40
        memory.size
        i64.extend_i32_u
        i64.sub
        i32.wrap_i64
        memory.grow
        i32.const -1
        i32.eq
        if ;; label = @3
          unreachable
        end
      end
      global.get 0
      i64.const 48
      i64.add
      local.set 41
      local.get 39
      global.set 0
      local.get 41
      i64.const 48
      i64.sub
      i32.wrap_i64
      i64.const 5501223100278326855
      i64.store
      local.get 41
      i64.const 40
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 41
      i64.const 32
      i64.sub
      i32.wrap_i64
      local.get 36
      i64.store
      local.get 41
      i64.const 24
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 41
      i64.const 16
      i64.sub
      i32.wrap_i64
      i64.const 4
      i64.store
      local.get 41
      i64.const 8
      i64.sub
      i32.wrap_i64
      i64.const 8
      i64.store
    end
    global.get 2
    i64.const 1
    i64.add
    global.set 2
    local.get 41
    local.set 29
    local.get 29
    i64.const 0
    i64.add
    i32.wrap_i64
    local.get 30
    i64.store
    local.get 29
    i64.const 8
    i64.add
    i32.wrap_i64
    local.get 31
    i64.store
    local.get 29
    i64.const 16
    i64.add
    i32.wrap_i64
    local.get 32
    i64.store
    local.get 29
    i64.const 24
    i64.add
    i32.wrap_i64
    local.get 33
    i64.store
    local.get 33
    local.set 34
    local.get 34
    i64.const 0
    i64.ne
    if ;; label = @1
      local.get 34
      i64.const 48
      i64.sub
      i32.wrap_i64
      i64.load
      i64.const 5501223100278326855
      i64.ne
      if ;; label = @2
        unreachable
      end
      local.get 34
      i64.const 40
      i64.sub
      i32.wrap_i64
      i64.load
      local.set 35
      local.get 35
      i64.const 0
      i64.eq
      if ;; label = @2
        unreachable
      end
      global.get 3
      i64.const 1
      i64.add
      global.set 3
      local.get 34
      i64.const 40
      i64.sub
      i32.wrap_i64
      local.get 35
      i64.const 1
      i64.add
      i64.store
    end
    local.get 29
    local.set 26
    i64.const 32
    i64.const 7
    i64.add
    i64.const 8
    i64.div_u
    i64.const 8
    i64.mul
    local.set 29
    local.get 29
    i64.const 8
    i64.lt_u
    if ;; label = @1
      i64.const 8
      local.set 29
    end
    i64.const 0
    local.set 34
    i64.const 0
    local.set 30
    global.get 1
    local.set 31
    block ;; label = @1
      loop ;; label = @2
        local.get 31
        i64.const 0
        i64.eq
        br_if 1 (;@1;)
        local.get 34
        i64.const 0
        i64.ne
        br_if 1 (;@1;)
        local.get 31
        i64.const 32
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 32
        local.get 31
        i64.const 8
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 33
        local.get 32
        local.get 29
        i64.ge_u
        if ;; label = @3
          local.get 30
          i64.const 0
          i64.eq
          if ;; label = @4
            local.get 33
            global.set 1
          else
            local.get 30
            i64.const 8
            i64.sub
            i32.wrap_i64
            local.get 33
            i64.store
          end
          local.get 31
          i64.const 48
          i64.sub
          i32.wrap_i64
          i64.const 5501223100278326855
          i64.store
          local.get 31
          i64.const 40
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 31
          i64.const 32
          i64.sub
          i32.wrap_i64
          local.get 32
          i64.store
          local.get 31
          i64.const 24
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 31
          i64.const 16
          i64.sub
          i32.wrap_i64
          i64.const 4
          i64.store
          local.get 31
          i64.const 8
          i64.sub
          i32.wrap_i64
          i64.const 8
          i64.store
          local.get 31
          local.set 34
        else
          local.get 31
          local.set 30
          local.get 33
          local.set 31
        end
        br 0 (;@2;)
      end
    end
    local.get 34
    i64.const 0
    i64.eq
    if ;; label = @1
      global.get 0
      i64.const 48
      i64.add
      local.get 29
      i64.add
      local.tee 32
      global.get 0
      i64.lt_u
      if ;; label = @2
        unreachable
      end
      local.get 32
      i64.const 1
      i64.sub
      i64.const 65536
      i64.div_u
      i64.const 1
      i64.add
      local.set 33
      memory.size
      i64.extend_i32_u
      local.get 33
      i64.lt_u
      if ;; label = @2
        local.get 33
        memory.size
        i64.extend_i32_u
        i64.sub
        i32.wrap_i64
        memory.grow
        i32.const -1
        i32.eq
        if ;; label = @3
          unreachable
        end
      end
      global.get 0
      i64.const 48
      i64.add
      local.set 34
      local.get 32
      global.set 0
      local.get 34
      i64.const 48
      i64.sub
      i32.wrap_i64
      i64.const 5501223100278326855
      i64.store
      local.get 34
      i64.const 40
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 34
      i64.const 32
      i64.sub
      i32.wrap_i64
      local.get 29
      i64.store
      local.get 34
      i64.const 24
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 34
      i64.const 16
      i64.sub
      i32.wrap_i64
      i64.const 4
      i64.store
      local.get 34
      i64.const 8
      i64.sub
      i32.wrap_i64
      i64.const 8
      i64.store
    end
    global.get 2
    i64.const 1
    i64.add
    global.set 2
    local.get 34
    local.set 22
    local.get 22
    i64.const 0
    i64.add
    i32.wrap_i64
    local.get 23
    i64.store
    local.get 22
    i64.const 8
    i64.add
    i32.wrap_i64
    local.get 24
    i64.store
    local.get 22
    i64.const 16
    i64.add
    i32.wrap_i64
    local.get 25
    i64.store
    local.get 22
    i64.const 24
    i64.add
    i32.wrap_i64
    local.get 26
    i64.store
    local.get 22
    local.set 19
    i64.const 32
    i64.const 7
    i64.add
    i64.const 8
    i64.div_u
    i64.const 8
    i64.mul
    local.set 22
    local.get 22
    i64.const 8
    i64.lt_u
    if ;; label = @1
      i64.const 8
      local.set 22
    end
    i64.const 0
    local.set 27
    i64.const 0
    local.set 23
    global.get 1
    local.set 24
    block ;; label = @1
      loop ;; label = @2
        local.get 24
        i64.const 0
        i64.eq
        br_if 1 (;@1;)
        local.get 27
        i64.const 0
        i64.ne
        br_if 1 (;@1;)
        local.get 24
        i64.const 32
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 25
        local.get 24
        i64.const 8
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 26
        local.get 25
        local.get 22
        i64.ge_u
        if ;; label = @3
          local.get 23
          i64.const 0
          i64.eq
          if ;; label = @4
            local.get 26
            global.set 1
          else
            local.get 23
            i64.const 8
            i64.sub
            i32.wrap_i64
            local.get 26
            i64.store
          end
          local.get 24
          i64.const 48
          i64.sub
          i32.wrap_i64
          i64.const 5501223100278326855
          i64.store
          local.get 24
          i64.const 40
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 24
          i64.const 32
          i64.sub
          i32.wrap_i64
          local.get 25
          i64.store
          local.get 24
          i64.const 24
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 24
          i64.const 16
          i64.sub
          i32.wrap_i64
          i64.const 4
          i64.store
          local.get 24
          i64.const 8
          i64.sub
          i32.wrap_i64
          i64.const 8
          i64.store
          local.get 24
          local.set 27
        else
          local.get 24
          local.set 23
          local.get 26
          local.set 24
        end
        br 0 (;@2;)
      end
    end
    local.get 27
    i64.const 0
    i64.eq
    if ;; label = @1
      global.get 0
      i64.const 48
      i64.add
      local.get 22
      i64.add
      local.tee 25
      global.get 0
      i64.lt_u
      if ;; label = @2
        unreachable
      end
      local.get 25
      i64.const 1
      i64.sub
      i64.const 65536
      i64.div_u
      i64.const 1
      i64.add
      local.set 26
      memory.size
      i64.extend_i32_u
      local.get 26
      i64.lt_u
      if ;; label = @2
        local.get 26
        memory.size
        i64.extend_i32_u
        i64.sub
        i32.wrap_i64
        memory.grow
        i32.const -1
        i32.eq
        if ;; label = @3
          unreachable
        end
      end
      global.get 0
      i64.const 48
      i64.add
      local.set 27
      local.get 25
      global.set 0
      local.get 27
      i64.const 48
      i64.sub
      i32.wrap_i64
      i64.const 5501223100278326855
      i64.store
      local.get 27
      i64.const 40
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 27
      i64.const 32
      i64.sub
      i32.wrap_i64
      local.get 22
      i64.store
      local.get 27
      i64.const 24
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 27
      i64.const 16
      i64.sub
      i32.wrap_i64
      i64.const 4
      i64.store
      local.get 27
      i64.const 8
      i64.sub
      i32.wrap_i64
      i64.const 8
      i64.store
    end
    global.get 2
    i64.const 1
    i64.add
    global.set 2
    local.get 27
    local.set 15
    local.get 15
    i64.const 0
    i64.add
    i32.wrap_i64
    local.get 16
    i64.store
    local.get 15
    i64.const 8
    i64.add
    i32.wrap_i64
    local.get 17
    i64.store
    local.get 15
    i64.const 16
    i64.add
    i32.wrap_i64
    local.get 18
    i64.store
    local.get 15
    i64.const 24
    i64.add
    i32.wrap_i64
    local.get 19
    i64.store
    local.get 15
    local.set 12
    i64.const 32
    i64.const 7
    i64.add
    i64.const 8
    i64.div_u
    i64.const 8
    i64.mul
    local.set 15
    local.get 15
    i64.const 8
    i64.lt_u
    if ;; label = @1
      i64.const 8
      local.set 15
    end
    i64.const 0
    local.set 20
    i64.const 0
    local.set 16
    global.get 1
    local.set 17
    block ;; label = @1
      loop ;; label = @2
        local.get 17
        i64.const 0
        i64.eq
        br_if 1 (;@1;)
        local.get 20
        i64.const 0
        i64.ne
        br_if 1 (;@1;)
        local.get 17
        i64.const 32
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 18
        local.get 17
        i64.const 8
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 19
        local.get 18
        local.get 15
        i64.ge_u
        if ;; label = @3
          local.get 16
          i64.const 0
          i64.eq
          if ;; label = @4
            local.get 19
            global.set 1
          else
            local.get 16
            i64.const 8
            i64.sub
            i32.wrap_i64
            local.get 19
            i64.store
          end
          local.get 17
          i64.const 48
          i64.sub
          i32.wrap_i64
          i64.const 5501223100278326855
          i64.store
          local.get 17
          i64.const 40
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 17
          i64.const 32
          i64.sub
          i32.wrap_i64
          local.get 18
          i64.store
          local.get 17
          i64.const 24
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 17
          i64.const 16
          i64.sub
          i32.wrap_i64
          i64.const 4
          i64.store
          local.get 17
          i64.const 8
          i64.sub
          i32.wrap_i64
          i64.const 8
          i64.store
          local.get 17
          local.set 20
        else
          local.get 17
          local.set 16
          local.get 19
          local.set 17
        end
        br 0 (;@2;)
      end
    end
    local.get 20
    i64.const 0
    i64.eq
    if ;; label = @1
      global.get 0
      i64.const 48
      i64.add
      local.get 15
      i64.add
      local.tee 18
      global.get 0
      i64.lt_u
      if ;; label = @2
        unreachable
      end
      local.get 18
      i64.const 1
      i64.sub
      i64.const 65536
      i64.div_u
      i64.const 1
      i64.add
      local.set 19
      memory.size
      i64.extend_i32_u
      local.get 19
      i64.lt_u
      if ;; label = @2
        local.get 19
        memory.size
        i64.extend_i32_u
        i64.sub
        i32.wrap_i64
        memory.grow
        i32.const -1
        i32.eq
        if ;; label = @3
          unreachable
        end
      end
      global.get 0
      i64.const 48
      i64.add
      local.set 20
      local.get 18
      global.set 0
      local.get 20
      i64.const 48
      i64.sub
      i32.wrap_i64
      i64.const 5501223100278326855
      i64.store
      local.get 20
      i64.const 40
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 20
      i64.const 32
      i64.sub
      i32.wrap_i64
      local.get 15
      i64.store
      local.get 20
      i64.const 24
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 20
      i64.const 16
      i64.sub
      i32.wrap_i64
      i64.const 4
      i64.store
      local.get 20
      i64.const 8
      i64.sub
      i32.wrap_i64
      i64.const 8
      i64.store
    end
    global.get 2
    i64.const 1
    i64.add
    global.set 2
    local.get 20
    local.set 8
    local.get 8
    i64.const 0
    i64.add
    i32.wrap_i64
    local.get 9
    i64.store
    local.get 8
    i64.const 8
    i64.add
    i32.wrap_i64
    local.get 10
    i64.store
    local.get 8
    i64.const 16
    i64.add
    i32.wrap_i64
    local.get 11
    i64.store
    local.get 8
    i64.const 24
    i64.add
    i32.wrap_i64
    local.get 12
    i64.store
    local.get 8
    local.set 5
    i64.const 32
    i64.const 7
    i64.add
    i64.const 8
    i64.div_u
    i64.const 8
    i64.mul
    local.set 8
    local.get 8
    i64.const 8
    i64.lt_u
    if ;; label = @1
      i64.const 8
      local.set 8
    end
    i64.const 0
    local.set 13
    i64.const 0
    local.set 9
    global.get 1
    local.set 10
    block ;; label = @1
      loop ;; label = @2
        local.get 10
        i64.const 0
        i64.eq
        br_if 1 (;@1;)
        local.get 13
        i64.const 0
        i64.ne
        br_if 1 (;@1;)
        local.get 10
        i64.const 32
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 11
        local.get 10
        i64.const 8
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 12
        local.get 11
        local.get 8
        i64.ge_u
        if ;; label = @3
          local.get 9
          i64.const 0
          i64.eq
          if ;; label = @4
            local.get 12
            global.set 1
          else
            local.get 9
            i64.const 8
            i64.sub
            i32.wrap_i64
            local.get 12
            i64.store
          end
          local.get 10
          i64.const 48
          i64.sub
          i32.wrap_i64
          i64.const 5501223100278326855
          i64.store
          local.get 10
          i64.const 40
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 10
          i64.const 32
          i64.sub
          i32.wrap_i64
          local.get 11
          i64.store
          local.get 10
          i64.const 24
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 10
          i64.const 16
          i64.sub
          i32.wrap_i64
          i64.const 4
          i64.store
          local.get 10
          i64.const 8
          i64.sub
          i32.wrap_i64
          i64.const 8
          i64.store
          local.get 10
          local.set 13
        else
          local.get 10
          local.set 9
          local.get 12
          local.set 10
        end
        br 0 (;@2;)
      end
    end
    local.get 13
    i64.const 0
    i64.eq
    if ;; label = @1
      global.get 0
      i64.const 48
      i64.add
      local.get 8
      i64.add
      local.tee 11
      global.get 0
      i64.lt_u
      if ;; label = @2
        unreachable
      end
      local.get 11
      i64.const 1
      i64.sub
      i64.const 65536
      i64.div_u
      i64.const 1
      i64.add
      local.set 12
      memory.size
      i64.extend_i32_u
      local.get 12
      i64.lt_u
      if ;; label = @2
        local.get 12
        memory.size
        i64.extend_i32_u
        i64.sub
        i32.wrap_i64
        memory.grow
        i32.const -1
        i32.eq
        if ;; label = @3
          unreachable
        end
      end
      global.get 0
      i64.const 48
      i64.add
      local.set 13
      local.get 11
      global.set 0
      local.get 13
      i64.const 48
      i64.sub
      i32.wrap_i64
      i64.const 5501223100278326855
      i64.store
      local.get 13
      i64.const 40
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 13
      i64.const 32
      i64.sub
      i32.wrap_i64
      local.get 8
      i64.store
      local.get 13
      i64.const 24
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 13
      i64.const 16
      i64.sub
      i32.wrap_i64
      i64.const 4
      i64.store
      local.get 13
      i64.const 8
      i64.sub
      i32.wrap_i64
      i64.const 8
      i64.store
    end
    global.get 2
    i64.const 1
    i64.add
    global.set 2
    local.get 13
    local.set 1
    local.get 1
    i64.const 0
    i64.add
    i32.wrap_i64
    local.get 2
    i64.store
    local.get 1
    i64.const 8
    i64.add
    i32.wrap_i64
    local.get 3
    i64.store
    local.get 1
    i64.const 16
    i64.add
    i32.wrap_i64
    local.get 4
    i64.store
    local.get 1
    i64.const 24
    i64.add
    i32.wrap_i64
    local.get 5
    i64.store
    local.get 1
    local.set 0
    local.get 0
  )
  (func (;2;) (type 2) (param i64) (result i64)
    (local i64 i64 i64 i64 i64)
    call 1
    local.set 1
    local.get 1
    local.set 2
    local.get 0
    local.set 3
    local.get 2
    local.get 3
    call 0
    local.set 4
    local.get 4
    local.set 5
    local.get 5
  )
  (func (;3;) (type 3) (param i64 i64) (result i64)
    (local i64 i64 i64 i64 i64 i64)
    local.get 0
    local.set 2
    local.get 2
    local.set 7
    local.get 7
    i64.const 0
    i64.add
    i32.wrap_i64
    i64.load
    i64.const 0
    i64.eq
    if ;; label = @1
      i64.const 0
      local.set 6
    else
      local.get 2
      local.set 7
      local.get 7
      i64.const 8
      i64.add
      i32.wrap_i64
      i64.load
      local.get 1
      i64.eq
      if (result i64) ;; label = @2
        i64.const 1
      else
        i64.const 0
      end
      i64.const 0
      i64.eq
      i32.eqz
      if (result i64) ;; label = @2
        i64.const 1
      else
        i64.const 0
      end
      i64.const 1
      i64.eq
      if (result i64) ;; label = @2
        i64.const 1
      else
        i64.const 0
      end
      i64.const 0
      i64.eq
      i32.eqz
      if ;; label = @2
        local.get 2
        local.set 7
        local.get 7
        i64.const 16
        i64.add
        i32.wrap_i64
        i64.load
        local.set 6
      else
        local.get 2
        local.set 7
        local.get 7
        i64.const 24
        i64.add
        i32.wrap_i64
        i64.load
        local.set 3
        local.get 1
        local.set 4
        local.get 3
        local.get 4
        call 3
        local.set 5
        local.get 5
        local.set 6
      end
    end
    local.get 6
  )
  (func (;4;) (type 4) (param i64) (result i64)
    (local i64 i64 i64 i64 i64 i64)
    local.get 0
    i64.const 7
    i64.add
    i64.const 8
    i64.div_u
    i64.const 8
    i64.mul
    local.set 1
    local.get 1
    i64.const 8
    i64.lt_u
    if ;; label = @1
      i64.const 8
      local.set 1
    end
    i64.const 0
    local.set 6
    i64.const 0
    local.set 2
    global.get 1
    local.set 3
    block ;; label = @1
      loop ;; label = @2
        local.get 3
        i64.const 0
        i64.eq
        br_if 1 (;@1;)
        local.get 6
        i64.const 0
        i64.ne
        br_if 1 (;@1;)
        local.get 3
        i64.const 32
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 4
        local.get 3
        i64.const 8
        i64.sub
        i32.wrap_i64
        i64.load
        local.set 5
        local.get 4
        local.get 1
        i64.ge_u
        if ;; label = @3
          local.get 2
          i64.const 0
          i64.eq
          if ;; label = @4
            local.get 5
            global.set 1
          else
            local.get 2
            i64.const 8
            i64.sub
            i32.wrap_i64
            local.get 5
            i64.store
          end
          local.get 3
          i64.const 48
          i64.sub
          i32.wrap_i64
          i64.const 5501223100278326855
          i64.store
          local.get 3
          i64.const 40
          i64.sub
          i32.wrap_i64
          i64.const 1
          i64.store
          local.get 3
          i64.const 32
          i64.sub
          i32.wrap_i64
          local.get 4
          i64.store
          local.get 3
          i64.const 24
          i64.sub
          i32.wrap_i64
          i64.const 0
          i64.store
          local.get 3
          i64.const 16
          i64.sub
          i32.wrap_i64
          i64.const 0
          i64.store
          local.get 3
          i64.const 8
          i64.sub
          i32.wrap_i64
          i64.const 0
          i64.store
          local.get 3
          local.set 6
        else
          local.get 3
          local.set 2
          local.get 5
          local.set 3
        end
        br 0 (;@2;)
      end
    end
    local.get 6
    i64.const 0
    i64.eq
    if ;; label = @1
      global.get 0
      i64.const 48
      i64.add
      local.get 1
      i64.add
      local.tee 4
      global.get 0
      i64.lt_u
      if ;; label = @2
        unreachable
      end
      local.get 4
      i64.const 1
      i64.sub
      i64.const 65536
      i64.div_u
      i64.const 1
      i64.add
      local.set 5
      memory.size
      i64.extend_i32_u
      local.get 5
      i64.lt_u
      if ;; label = @2
        local.get 5
        memory.size
        i64.extend_i32_u
        i64.sub
        i32.wrap_i64
        memory.grow
        i32.const -1
        i32.eq
        if ;; label = @3
          unreachable
        end
      end
      global.get 0
      i64.const 48
      i64.add
      local.set 6
      local.get 4
      global.set 0
      local.get 6
      i64.const 48
      i64.sub
      i32.wrap_i64
      i64.const 5501223100278326855
      i64.store
      local.get 6
      i64.const 40
      i64.sub
      i32.wrap_i64
      i64.const 1
      i64.store
      local.get 6
      i64.const 32
      i64.sub
      i32.wrap_i64
      local.get 1
      i64.store
      local.get 6
      i64.const 24
      i64.sub
      i32.wrap_i64
      i64.const 0
      i64.store
      local.get 6
      i64.const 16
      i64.sub
      i32.wrap_i64
      i64.const 0
      i64.store
      local.get 6
      i64.const 8
      i64.sub
      i32.wrap_i64
      i64.const 0
      i64.store
    end
    global.get 2
    i64.const 1
    i64.add
    global.set 2
    local.get 6
  )
  (func (;5;) (type 5)
    i64.const 4096
    global.set 0
    i64.const 0
    global.set 1
    i64.const 0
    global.set 2
    i64.const 0
    global.set 3
    i64.const 0
    global.set 4
    i64.const 0
    global.set 5
  )
  (func (;6;) (type 6) (param i64) (result i64)
    (local i64)
    local.get 0
    i64.const 0
    i64.ne
    if ;; label = @1
      local.get 0
      i64.const 48
      i64.sub
      i32.wrap_i64
      i64.load
      i64.const 5501223100278326855
      i64.ne
      if ;; label = @2
        unreachable
      end
      local.get 0
      i64.const 40
      i64.sub
      i32.wrap_i64
      i64.load
      local.set 1
      local.get 1
      i64.const 0
      i64.eq
      if ;; label = @2
        unreachable
      end
      global.get 3
      i64.const 1
      i64.add
      global.set 3
      local.get 0
      i64.const 40
      i64.sub
      i32.wrap_i64
      local.get 1
      i64.const 1
      i64.add
      i64.store
    end
    local.get 0
  )
  (func (;7;) (type 7) (param i64)
    (local i64 i64 i64 i64 i64 i64 i64 i64)
    local.get 0
    i64.const 0
    i64.eq
    if ;; label = @1
      return
    end
    local.get 0
    i64.const 48
    i64.sub
    i32.wrap_i64
    i64.load
    i64.const 5501223100278326855
    i64.ne
    if ;; label = @1
      unreachable
    end
    local.get 0
    i64.const 40
    i64.sub
    i32.wrap_i64
    i64.load
    local.set 1
    local.get 1
    i64.const 0
    i64.eq
    if ;; label = @1
      unreachable
    end
    global.get 4
    i64.const 1
    i64.add
    global.set 4
    i64.const 1
    local.get 1
    i64.lt_u
    if ;; label = @1
      local.get 0
      i64.const 40
      i64.sub
      i32.wrap_i64
      local.get 1
      i64.const 1
      i64.sub
      i64.store
      return
    end
    local.get 0
    i64.const 24
    i64.sub
    i32.wrap_i64
    i64.load
    local.set 2
    local.get 2
    i64.const 1
    i64.eq
    if ;; label = @1
      local.get 0
      i64.const 16
      i64.sub
      i32.wrap_i64
      i64.load
      local.set 3
      local.get 0
      i64.const 8
      i64.sub
      i32.wrap_i64
      i64.load
      local.set 5
      i64.const 0
      local.set 6
      block ;; label = @2
        loop ;; label = @3
          local.get 6
          local.get 3
          i64.ge_u
          br_if 1 (;@2;)
          local.get 5
          local.get 6
          i64.shr_u
          i64.const 1
          i64.and
          i64.const 0
          i64.ne
          if ;; label = @4
            local.get 0
            local.get 6
            i64.const 8
            i64.mul
            i64.add
            i32.wrap_i64
            i64.load
            local.set 8
            local.get 8
            call 7
          end
          local.get 6
          i64.const 1
          i64.add
          local.set 6
          br 0 (;@3;)
        end
      end
    end
    local.get 2
    i64.const 2
    i64.eq
    if ;; label = @1
      local.get 0
      i32.wrap_i64
      i64.load
      local.set 3
      local.get 0
      i64.const 16
      i64.sub
      i32.wrap_i64
      i64.load
      local.set 4
      local.get 0
      i64.const 8
      i64.sub
      i32.wrap_i64
      i64.load
      local.set 5
      i64.const 0
      local.set 7
      block ;; label = @2
        loop ;; label = @3
          local.get 7
          local.get 3
          i64.ge_u
          br_if 1 (;@2;)
          i64.const 0
          local.set 6
          block ;; label = @4
            loop ;; label = @5
              local.get 6
              local.get 4
              i64.ge_u
              br_if 1 (;@4;)
              local.get 5
              local.get 6
              i64.shr_u
              i64.const 1
              i64.and
              i64.const 0
              i64.ne
              if ;; label = @6
                local.get 0
                i64.const 8
                i64.add
                local.get 7
                local.get 4
                i64.mul
                local.get 6
                i64.add
                i64.const 8
                i64.mul
                i64.add
                i32.wrap_i64
                i64.load
                local.set 8
                local.get 8
                call 7
              end
              local.get 6
              i64.const 1
              i64.add
              local.set 6
              br 0 (;@5;)
            end
          end
          local.get 7
          i64.const 1
          i64.add
          local.set 7
          br 0 (;@3;)
        end
      end
    end
    global.get 5
    i64.const 1
    i64.add
    global.set 5
    local.get 0
    i64.const 40
    i64.sub
    i32.wrap_i64
    i64.const 0
    i64.store
    local.get 0
    i64.const 8
    i64.sub
    i32.wrap_i64
    global.get 1
    i64.store
    local.get 0
    global.set 1
  )
)
