import Collatz.MCycle110Certs114

/-!
# Certificates of the listed shapes of `data110`, chunks 456..459
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_456 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_456 = true := by
  decide +kernel

theorem certs110_457 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_457 = true := by
  decide +kernel

theorem certs110_458 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_458 = true := by
  decide +kernel

theorem certs110_459 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_459 = true := by
  decide +kernel

end Collatz
