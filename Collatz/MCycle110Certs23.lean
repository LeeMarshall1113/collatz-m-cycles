import Collatz.MCycle110Certs22

/-!
# Certificates of the listed shapes of `data110`, chunks 88..91
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_88 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_88 = true := by
  decide +kernel

theorem certs110_89 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_89 = true := by
  decide +kernel

theorem certs110_90 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_90 = true := by
  decide +kernel

theorem certs110_91 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_91 = true := by
  decide +kernel

end Collatz
