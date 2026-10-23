import Collatz.MCycle110Certs96

/-!
# Certificates of the listed shapes of `data110`, chunks 384..387
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_384 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_384 = true := by
  decide +kernel

theorem certs110_385 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_385 = true := by
  decide +kernel

theorem certs110_386 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_386 = true := by
  decide +kernel

theorem certs110_387 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_387 = true := by
  decide +kernel

end Collatz
