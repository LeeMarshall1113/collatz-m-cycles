import Collatz.MCycle110Certs40

/-!
# Certificates of the listed shapes of `data110`, chunks 160..163
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_160 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_160 = true := by
  decide +kernel

theorem certs110_161 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_161 = true := by
  decide +kernel

theorem certs110_162 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_162 = true := by
  decide +kernel

theorem certs110_163 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_163 = true := by
  decide +kernel

end Collatz
