kind: fix

A foreign function whose result writes, as `extern fn f(p: c.Ptr<u8>) -> inout c.Ptr<u8>`, is E0353 at the result's type under the reference interpreter too, as under the compiler: C gives no place a projection could yield.
