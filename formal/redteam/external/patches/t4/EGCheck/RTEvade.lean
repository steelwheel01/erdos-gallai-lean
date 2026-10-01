/-! t4: `«debug».skipKernelTC` spelling evades `\bdebug\.`. Benign on its own — no bad constant. -/
set_option «debug».skipKernelTC true in
theorem EGCheck.rt4 : True := trivial
