import Collatz.MCycle110Certs37

/-!
# Certificates of the listed shapes of `data110`, chunks 148..151
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_148 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_148 = true := by
  decide +kernel

theorem certs110_149 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_149 = true := by
  decide +kernel

theorem certs110_150 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_150 = true := by
  decide +kernel

theorem certs110_151 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_151 = true := by
  decide +kernel

end Collatz
