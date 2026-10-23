import Collatz.MCycle110Certs23

/-!
# Certificates of the listed shapes of `data110`, chunks 92..95
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_92 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_92 = true := by
  decide +kernel

theorem certs110_93 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_93 = true := by
  decide +kernel

theorem certs110_94 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_94 = true := by
  decide +kernel

theorem certs110_95 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_95 = true := by
  decide +kernel

end Collatz
