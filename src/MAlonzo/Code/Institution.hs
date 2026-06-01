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

module MAlonzo.Code.Institution where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agent
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Proposal

-- Institution.BuyerAdmissible
d_BuyerAdmissible_6 a0 a1 = ()
data T_BuyerAdmissible_6
  = C_constructor_20 MAlonzo.Code.Data.Rational.Base.T__'8804'__54
                     MAlonzo.Code.Data.Rational.Base.T__'8804'__54
-- Institution.BuyerAdmissible.bidBelowValue
d_bidBelowValue_16 ::
  T_BuyerAdmissible_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_bidBelowValue_16 v0
  = case coe v0 of
      C_constructor_20 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.BuyerAdmissible.bidWithinBudget
d_bidWithinBudget_18 ::
  T_BuyerAdmissible_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_bidWithinBudget_18 v0
  = case coe v0 of
      C_constructor_20 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.SellerAdmissible
d_SellerAdmissible_26 a0 a1 = ()
data T_SellerAdmissible_26
  = C_constructor_40 MAlonzo.Code.Data.Rational.Base.T__'8804'__54
                     MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Institution.SellerAdmissible.askAboveValue
d_askAboveValue_36 ::
  T_SellerAdmissible_26 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_askAboveValue_36 v0
  = case coe v0 of
      C_constructor_40 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.SellerAdmissible.hasInventory
d_hasInventory_38 ::
  T_SellerAdmissible_26 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_hasInventory_38 v0
  = case coe v0 of
      C_constructor_40 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match
d_Match_42 = ()
data T_Match_42
  = C_constructor_80 MAlonzo.Code.Agent.T_Agent_18
                     MAlonzo.Code.Agent.T_Agent_18 MAlonzo.Code.Proposal.T_Proposal_2
                     MAlonzo.Code.Proposal.T_Proposal_2 T_BuyerAdmissible_6
                     T_SellerAdmissible_26 MAlonzo.Code.Data.Rational.Base.T__'8804'__54
                     MAlonzo.Code.Data.Rational.Base.T_ℚ_6
                     MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Institution.Match.buyer
d_buyer_62 :: T_Match_42 -> MAlonzo.Code.Agent.T_Agent_18
d_buyer_62 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match.seller
d_seller_64 :: T_Match_42 -> MAlonzo.Code.Agent.T_Agent_18
d_seller_64 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match.bid
d_bid_66 :: T_Match_42 -> MAlonzo.Code.Proposal.T_Proposal_2
d_bid_66 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match.ask
d_ask_68 :: T_Match_42 -> MAlonzo.Code.Proposal.T_Proposal_2
d_ask_68 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match.buyerAdm
d_buyerAdm_70 :: T_Match_42 -> T_BuyerAdmissible_6
d_buyerAdm_70 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match.sellerAdm
d_sellerAdm_72 :: T_Match_42 -> T_SellerAdmissible_26
d_sellerAdm_72 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match.crosses
d_crosses_74 ::
  T_Match_42 -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_crosses_74 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match.clearingPrice
d_clearingPrice_76 ::
  T_Match_42 -> MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_clearingPrice_76 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.Match.priceInRange
d_priceInRange_78 ::
  T_Match_42 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_priceInRange_78 v0
  = case coe v0 of
      C_constructor_80 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Institution.valuationChain
d_valuationChain_84 ::
  T_Match_42 -> MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_valuationChain_84 v0
  = coe
      MAlonzo.Code.Data.Rational.Properties.d_'8804''45'trans_3608
      (MAlonzo.Code.Agent.d_unitValue_12
         (coe MAlonzo.Code.Agent.d_valuation_34 (coe d_seller_64 (coe v0))))
      (MAlonzo.Code.Proposal.d_price_12 (coe d_bid_66 (coe v0)))
      (MAlonzo.Code.Agent.d_unitValue_12
         (coe MAlonzo.Code.Agent.d_valuation_34 (coe d_buyer_62 (coe v0))))
      (coe
         MAlonzo.Code.Data.Rational.Properties.d_'8804''45'trans_3608
         (MAlonzo.Code.Agent.d_unitValue_12
            (coe MAlonzo.Code.Agent.d_valuation_34 (coe d_seller_64 (coe v0))))
         (MAlonzo.Code.Proposal.d_price_12 (coe d_ask_68 (coe v0)))
         (MAlonzo.Code.Proposal.d_price_12 (coe d_bid_66 (coe v0)))
         (d_askAboveValue_36 (coe d_sellerAdm_72 (coe v0)))
         (d_crosses_74 (coe v0)))
      (d_bidBelowValue_16 (coe d_buyerAdm_70 (coe v0)))
