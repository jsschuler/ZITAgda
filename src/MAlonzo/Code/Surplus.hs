{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Surplus where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agent
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Institution

-- Surplus.p≤q⇒0≤q-p
d_p'8804'q'8658'0'8804'q'45'p_6 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_p'8804'q'8658'0'8804'q'45'p_6 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Properties.d_'43''45'mono'737''45''8804'_4378
      (coe MAlonzo.Code.Data.Rational.Base.d_'45'__112 (coe v0)) (coe v0)
      (coe v1) (coe v2)
-- Surplus.surplus
d_surplus_16 ::
  MAlonzo.Code.Institution.T_Match_42 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_surplus_16 v0
  = coe
      MAlonzo.Code.Data.Rational.Base.d__'45'__282
      (coe
         MAlonzo.Code.Agent.d_unitValue_12
         (coe
            MAlonzo.Code.Agent.d_valuation_34
            (coe MAlonzo.Code.Institution.d_buyer_62 (coe v0))))
      (coe
         MAlonzo.Code.Agent.d_unitValue_12
         (coe
            MAlonzo.Code.Agent.d_valuation_34
            (coe MAlonzo.Code.Institution.d_seller_64 (coe v0))))
-- Surplus.surplusNonNeg
d_surplusNonNeg_22 ::
  MAlonzo.Code.Institution.T_Match_42 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_surplusNonNeg_22 v0
  = coe
      d_p'8804'q'8658'0'8804'q'45'p_6
      (coe
         MAlonzo.Code.Agent.d_unitValue_12
         (coe
            MAlonzo.Code.Agent.d_valuation_34
            (coe MAlonzo.Code.Institution.d_seller_64 (coe v0))))
      (coe
         MAlonzo.Code.Agent.d_unitValue_12
         (coe
            MAlonzo.Code.Agent.d_valuation_34
            (coe MAlonzo.Code.Institution.d_buyer_62 (coe v0))))
      (coe MAlonzo.Code.Institution.d_valuationChain_84 (coe v0))
