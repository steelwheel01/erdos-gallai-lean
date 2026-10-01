/-! IO: arbitrary file write at build time (opus E). The harness runs the build under a read-only
bind mount of the real repo, so a write into it FAILS (caught here so the build still succeeds);
a write into a scratch dir succeeds — proving the attack is real. The out-of-band statement/axiom
checks do not see it (there is no bad constant); lint and CI job separation cover build-time IO. -/
#eval (do
  let out := (← IO.getEnv "RT_IO_OUT").getD "/tmp"
  IO.FS.writeFile (out ++ "/rt_pwned.txt") "pwned at build time"
  match (← IO.getEnv "RT_REAL_TREE") with
  | some real =>
      try
        IO.FS.writeFile (real ++ "/formal/rt_pwned_real.txt") "written into the real tree"
        IO.println "WROTE REAL TREE"
      catch _ => IO.println "real tree is read-only (bind mount held)"
  | none => pure () : IO Unit)
theorem EGCheck.rtIO : True := trivial
