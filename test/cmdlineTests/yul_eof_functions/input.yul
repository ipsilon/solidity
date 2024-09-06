object "a" {
  code {
    error(f())

    function f() -> result
    {
        result := 1
    }

    function error(v)
    {
        mstore(0, v)
        revert(0, 32)
    }
  }
}

