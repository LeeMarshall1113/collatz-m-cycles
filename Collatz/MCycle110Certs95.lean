import Collatz.MCycle110Certs94

/-!
# Certificates of the listed shapes of `data110`, chunks 376..379
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_376 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_376 = true := by
  decide +kernel

theorem certs110_377 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_377 = true := by
  decide +kernel

theorem certs110_378 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_378 = true := by
  decide +kernel

theorem certs110_379 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_379 = true := by
  decide +kernel

end Collatz
