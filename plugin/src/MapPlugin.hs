{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

module MapPlugin ( plugin ) where

-- base
import Control.Arrow
  ( (***) )
import Control.Monad
  ( join )
import Data.Either
  ( partitionEithers )
import Data.Maybe
  ( catMaybes )

-- ghc
import qualified GHC
    ( Module, mkModuleName )
import qualified GHC.Builtin.Types
  as GHC
    ( promotedNothingDataCon, promotedJustDataCon )
import qualified GHC.Core
  as GHC
    ( Expr(Coercion) )
import qualified GHC.Core.Coercion
  as GHC
    ( Coercion, mkUnivCo, mkPrimEqPredRole )
{-
import qualified GHC.Core.DataCon
  as GHC
    ( promoteDataCon )
-}
import qualified GHC.Core.Predicate
  as GHC
    ( Pred(..), classifyPredType
    , EqRel(..)
    )
import qualified GHC.Core.TyCo.Rep
  as GHC
    ( Type(..)
    , UnivCoProvenance(..)
    )
import qualified GHC.Core.Type
  as GHC
    ( mkTyConApp )
import qualified GHC.Core.Unify
  as GHC
    ( tcMatchTy, typesCantMatch )
import qualified GHC.Driver.Finder
  as GHC
    ( FindResult(..) )
import qualified GHC.Data.FastString
  as GHC
    ( fsLit )
import qualified GHC.Plugins
  as GHC
    ( Plugin(..), defaultPlugin, purePlugin )
import qualified GHC.Core.DataCon
  as GHC
    ( DataCon )
import qualified GHC.Core.TyCon
  as GHC
    ( TyCon(..) )
import qualified GHC.Tc.Plugin
  as GHC
    ( findImportedModule
    , lookupOrig, tcLookupTyCon, tcLookupDataCon
    , newGiven
    )
import qualified GHC.Tc.Types
  as GHC
    ( TcPlugin(..)
    , TcPluginM
    , TcPluginResult(..)
    )
import qualified GHC.Tc.Types.Constraint
  as GHC
    ( Ct(..), ctPred, ctLoc
    , bumpCtLocDepth, mkNonCanonical
    )
import qualified GHC.Tc.Types.Evidence
  as GHC
    ( EvTerm, Role(..) )
import qualified GHC.Types.Name.Occurrence
  as GHC
    ( mkDataOcc, mkTcOcc )
import qualified GHC.Utils.Outputable
  as GHC
    ( ppr, pprTrace ) --, pprPanic )

--------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = tcPlugin
    , GHC.pluginRecompile = GHC.purePlugin
    }

tcPlugin :: [ String ] -> Maybe GHC.TcPlugin
tcPlugin _args =
  Just $
    GHC.TcPlugin
      { GHC.tcPluginInit  = tcPluginInit
      , GHC.tcPluginSolve = tcPluginSolve
      , GHC.tcPluginStop  = tcPluginStop
      }

data PluginDefs =
  PluginDefs
    { keyValTyCon     :: !GHC.TyCon
    , keyValDataCon   :: !GHC.DataCon
    , mapTyCon        :: !GHC.TyCon
    , fromListDataCon :: !GHC.DataCon
    , lookupTyCon     :: !GHC.TyCon
    , insertTyCon     :: !GHC.TyCon
    , deleteTyCon     :: !GHC.TyCon
    , unionTyCon      :: !GHC.TyCon
    , differenceTyCon :: !GHC.TyCon
    }

tcPluginInit :: GHC.TcPluginM PluginDefs
tcPluginInit = do
  dataTypeMapModule <- findModule "Map-Plugin" "Data.Type.Map"
  keyValTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   ":->"        )
  keyValDataCon   <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkDataOcc ":->"        )
  mapTyCon        <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Map"        )
  fromListDataCon <- GHC.tcLookupDataCon =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkDataOcc "FromList"   )
  lookupTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Lookup"     )
  insertTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Insert"     )
  deleteTyCon     <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Delete"     )
  unionTyCon      <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Union"      )
  differenceTyCon <- GHC.tcLookupTyCon   =<< GHC.lookupOrig dataTypeMapModule ( GHC.mkTcOcc   "Difference" )
  pure ( PluginDefs { .. } )

findModule :: String -> String -> GHC.TcPluginM GHC.Module
findModule pkg modName = do
  findResult <- GHC.findImportedModule ( GHC.mkModuleName modName ) ( Just $ GHC.fsLit pkg )
  case findResult of
    GHC.Found _ res     -> pure res
    GHC.FoundMultiple _ -> error $ "MapPlugin: found multiple modules named " <> modName <> "."
    _                   -> error $ "MapPlugin: could not find any module named " <> modName <> "."

tcPluginStop :: PluginDefs -> GHC.TcPluginM ()
tcPluginStop _ = pure ()

tcPluginSolve :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.TcPluginM GHC.TcPluginResult
tcPluginSolve _state _givens _deriveds []      = pure $ GHC.TcPluginOk [] []
tcPluginSolve  state  givens  deriveds wanteds = do
  ( contras, oks )
    <- GHC.pprTrace "Givens:"   ( GHC.ppr givens   )
    .  GHC.pprTrace "Deriveds:" ( GHC.ppr deriveds )
    .  GHC.pprTrace "Wanteds:"  ( GHC.ppr wanteds  )
    .  partitionEithers
    <$> traverse ( \ wanted -> specifyWanted wanted <$> solveWanted state givens deriveds wanted ) wanteds
  case contras of
    [] ->
      let
        solveds :: [ ( GHC.EvTerm, GHC.Ct ) ]
        news    :: [ GHC.Ct ]
        ( solveds, news ) = ( catMaybes *** join ) ( unzip oks )
      in  pure $ GHC.TcPluginOk solveds news
    _  -> pure $ GHC.TcPluginContradiction contras

data SolverResult
  = Unsolved
    { newCts   :: ![ GHC.Ct ] }
  | Solved
    { evidence :: !GHC.EvTerm
    , newCts   :: ![ GHC.Ct ]
    }
  | Contradiction

pattern Ignore :: SolverResult
pattern Ignore = Unsolved []

specifyWanted :: GHC.Ct -> SolverResult -> Either GHC.Ct ( Maybe ( GHC.EvTerm, GHC.Ct ), [ GHC.Ct ] )
specifyWanted _      ( Unsolved {..} ) = Right ( Nothing, newCts )
specifyWanted wanted ( Solved   {..} ) = Right ( Just ( evidence, wanted ), newCts )
specifyWanted wanted Contradiction     = Left wanted

solveWanted :: PluginDefs -> [ GHC.Ct ] -> [ GHC.Ct ] -> GHC.Ct -> GHC.TcPluginM SolverResult
solveWanted pluginDefs givens _deriveds wanted =
  case GHC.classifyPredType ( GHC.ctPred wanted ) of
    GHC.EqPred GHC.NomEq lhs rhs -> do
      newCts <- catMaybes <$> traverse ( simplify pluginDefs givens wanted ) [ lhs, rhs ]
      pure $ Unsolved {..}
    _ -> pure Ignore

-- | Try to simplify a type, e.g. simplify @ Lookup k ( Insert k v s ) @ to @ v @.
simplify :: PluginDefs -> [ GHC.Ct ] -> GHC.Ct -> GHC.Type -> GHC.TcPluginM ( Maybe GHC.Ct )
simplify pluginDefs@( PluginDefs { .. } ) givens wanted ty =
  case ty of
    -- Recognise one of the handled `TyCon`s (`Lookup`, `Insert`, ...)
    GHC.TyConApp tyCon args
      -- Fully saturated application of `Lookup` type family
      | tyCon == lookupTyCon
      , [ kind_k, kind_v, k, kvs ] <- args
      -> do
        simpl <- simplifyLookup pluginDefs givens k kvs
        case simpl of
          NoSimplification ->
            pure Nothing
          SimplifyArg arg  -> do
            let
              simplTy :: GHC.Type
              simplTy = GHC.mkTyConApp lookupTyCon [ kind_k, kind_v, k, arg ]
            Just <$> newDeducedGivenEq wanted ty simplTy
          Result ( Just res ) -> do
            let
              resTy :: GHC.Type
              resTy = GHC.mkTyConApp GHC.promotedJustDataCon [ kind_v, res ]
            Just <$> newDeducedGivenEq wanted ty resTy
          Result Nothing -> do
            let
              resTy :: GHC.Type
              resTy = GHC.mkTyConApp GHC.promotedNothingDataCon [ kind_v ]
            Just <$> newDeducedGivenEq wanted ty resTy
    _ -> pure Nothing

data TyFamAppSimplification arg res
  = NoSimplification
  | SimplifyArg arg
  | Result      res

newDeducedGivenEq :: GHC.Ct -> GHC.Type -> GHC.Type -> GHC.TcPluginM GHC.Ct
newDeducedGivenEq ct lhs rhs = do
  let
    coercion :: GHC.Coercion
    coercion = GHC.mkUnivCo ( GHC.PluginProv "Map-Plugin") GHC.Nominal lhs rhs
  evidence <-
    GHC.newGiven
      ( GHC.bumpCtLocDepth $ GHC.ctLoc ct )
      ( GHC.mkPrimEqPredRole GHC.Nominal lhs rhs )
      ( GHC.Coercion coercion )
  pure ( GHC.mkNonCanonical evidence )

-- | Tries to simplify a type family application @ Lookup k kvs @ (either computing the result or simplifying @ kvs @).
simplifyLookup :: PluginDefs -> [ GHC.Ct ] -> GHC.Type -> GHC.Type -> GHC.TcPluginM ( TyFamAppSimplification GHC.Type ( Maybe GHC.Type ) )
simplifyLookup pluginDefs@( PluginDefs { .. } ) givens k0 kvs0 =
  case kvs0 of
    GHC.TyConApp tyCon args
      | tyCon == insertTyCon
      , [ _kind_k, _kind_v, k1, v1, kvs1 ] <- args
      -> do
        mbEq <- eqTy pluginDefs givens k0 k1
        case mbEq of
          -- @ Lookup k0 ( Insert k1 v1 kvs1 ) ~ Just v1 @ when @ k0 ~ k1 @.
          Just True  -> pure ( Result $ Just v1 )
          -- @ Lookup k0 ( Insert k1 v1 kvs1 ) ~ Lookup k0 kvs1 @ when @ k0 /~ k1 @.
          Just False -> pure ( SimplifyArg kvs1 )
          Nothing    -> pure NoSimplification
      | tyCon == deleteTyCon
      , [ _kind_k, _kind_v, k1, kvs1 ] <- args
      -> do
        mbEq <- eqTy pluginDefs givens k0 k1
        case mbEq of
          -- @ Lookup k0 ( Delete k1 kvs1 ) ~ Nothing @ when @ k0 ~ k1 @.
          Just True  -> pure ( Result Nothing )
          -- @ Lookup k0 ( Delete k1 kvs1 ) ~ Lookup k0 kvs1 @ when @ k0 /~ k1 @.
          Just False -> pure ( SimplifyArg kvs1 )
          -- If we don't know whether @ k0 @ and @ k1 @ can unify,
          -- it is still worth trying to simplify @ kvs1 @, as @ Lookup k0 kvs1 ~ Nothing @
          -- would also imply that @ Lookup k0 ( Delete k1 kvs1 ) ~ Nothing @.
          Nothing    -> do
            simplFurther <- simplifyLookup pluginDefs givens k0 kvs1
            case simplFurther of
              Result Nothing -> pure ( Result Nothing )
              _              -> pure NoSimplification
      {-
      | tyCon == GHC.promoteDataCon fromListDataCon
      , [ _kind_k, _kind_v, list ] <- args
      -> listLookup pluginDefs givens k0 list
      -}
    _ -> pure NoSimplification

-- | Computes whether `lhs == rhs`.
--
--  - @ Just True @: types are equal,
--  - @ Just False @: types are apart,
--  - @ Nothing @: unknown at this stage.
eqTy :: PluginDefs -> [ GHC.Ct ] -> GHC.Type -> GHC.Type -> GHC.TcPluginM ( Maybe Bool )
eqTy ( PluginDefs {} ) _givens lhs rhs
  | Just _ <- GHC.tcMatchTy lhs rhs
  = pure $ Just True
  | GHC.typesCantMatch [ ( lhs, rhs ) ]
  = pure $ Just False
  | otherwise
  = pure $ Nothing
