import Data.Maybe
import Data.List
import Control.Applicative
import Debug.Trace

infixl 4 :@:
infixl 3 :-

data Pattern = P String [String] deriving (Eq)

data PatternMatch = Pattern :- Expr deriving (Eq)

data Expr = V String
          | C String [Expr]
          | L String Expr
          | F String
          | Expr :@: Expr
          | Case Expr [PatternMatch]
          | Let String Expr Expr
          deriving (Eq)

type Context = [(String, Expr)]


instance Show Expr where
    show (V name)          = name
    show c@(C name args) | isNum c = show $ e2i c
    show (C name args)     = name ++ "[" ++ (intercalate ", " (show <$> args)) ++ "]"
    show (L arg expr)      = "λ" ++ arg ++ "." ++ (show expr)
    show (l :@: r)         = "(" ++ (show l) ++ " " ++ (show r) ++ ")"  
    show (F name)          = name
    show (Let var e1 e2)   = "let " ++ var ++ " = " ++ (show e1) ++ " in " ++ (show e2)
    show (Case expr cases) = "case " ++ (show expr) ++ " of\n\t{\n" ++ (concatMap (\pm -> "\t\t" ++ (show pm) ++ "\n") cases) ++ "\t}"

instance Show Pattern where
    show (P name args) = name ++ "[" ++ (intercalate " " args) ++ "]"

instance Show PatternMatch where
    show (p :- e) = show p ++ " :- " ++ show e

getF :: Context -> String -> Expr
getF ctx name = fromMaybe (error $ "can't find " ++ name) $ lookup name ctx

isVal :: Expr -> Bool
isVal (L _ _)  = True
isVal (V _)    = True
isVal (C _ es) = all isVal es
isVal ((L _ _) :@: _) = False
isVal (e :@: _) = isVal e
isVal _      = False -- Let / F / Case

isMatchP :: Expr -> Pattern -> Bool
isMatchP (C name xs) (P pname pxs) = (pname == name) && (length pxs == length xs)
isMatchP _ _                       = False 

isMatch :: Expr -> PatternMatch -> Bool
isMatch e (p :- _) = isMatchP e p 


---------------------------------------------------------------------------

notInFreeVs :: String -> Expr -> Bool
notInFreeVs x e = notElem x $ freeVs e

freeIn :: String -> Expr -> Expr -> String
freeIn y e1 e2 = nextFree y $ (freeVs e1) ++ (freeVs e2)

freeIn2 :: String -> [String] -> Expr -> String
freeIn2 y f1 e2 = nextFree y $ f1 ++ (freeVs e2)

substXY :: String -> String -> String -> Expr -> Expr -> Expr
substXY x y t n e = subst x n $ subst y (V t) e

-- e[x <- n]
subst :: String -> Expr -> Expr -> Expr 
subst x n v@(V y)       = if y == x then n else v
subst x n (C s es)      = C s $ (subst x n) <$> es
subst x n l@(L y p)     
    | x == y || notInFreeVs x p = l
    | notInFreeVs y n           = L y (subst x n p)
    | otherwise                 = let t = freeIn y n p
                                    in L t $ substXY x y t n p
subst x n (F s)         = F s -- shouldn't contains free variables
subst x n (p :@: q)     = (subst x n p) :@: (subst x n q)
subst x n (Case e ps)   = Case (subst x n e) $ (substP x n) <$> ps
subst x n l@(Let y e1 e2) 
    | x == y || notInFreeVs x e2 = Let y (subst x n e1) e2
    | notInFreeVs y n            = Let y (subst x n e1) (subst x n e2)
    | otherwise                    = let t = freeIn y n e2 
                                     in Let t (subst x n e1) $ substXY x y t n e2

substP :: String -> Expr -> PatternMatch -> PatternMatch
substP y n p@(P c ys :- e0)
    | y `elem` ys || notInFreeVs y e0 = p
    | y `notElem` ys                  = P c ys :- subst y n e0 
    | otherwise                       = let (xs', e') = subst' ys e0 in P c xs' :- subst y n e'
        where
            fn = freeVs n
            subst' :: [String] -> Expr -> ([String], Expr)
            subst' []   e   = ([], e) 
            subst' (x:xs) e
                | x `elem` fn = let t = freeIn2 x fn e in
                                let (xs', e') = subst' xs (subst x (V t) e) in (t:xs', e')
                | otherwise   = let (xs', e') = subst' xs e in (x:xs', e')

substAll :: [String] -> [Expr] -> Expr -> Expr 
substAll xs ns e = foldl (\e' (x, n) -> subst x n e') e $ zip xs ns 

nextFree :: String -> [String] -> String
nextFree x xs = if x `elem` xs then nextFree (x ++ "'") xs else x

unionAll :: [[String]] -> [String]
unionAll x = foldr (\a b -> a `union` b) [] x

freeVs :: Expr -> [String] 
freeVs (V x)         = [x]
freeVs (C s es)      = unionAll $ freeVs <$> es
freeVs (L x y)       = (freeVs y) \\ [x]
freeVs (F s)         = []
freeVs (x :@: y)     = (freeVs x) `union` (freeVs y)
freeVs (Case e ps)   = (freeVs e) `union` (unionAll $ freeVsP <$> ps)
freeVs (Let x e1 e2) = (freeVs e1) `union` ((freeVs e2) \\ [x])

freeVsP :: PatternMatch -> [String]
freeVsP (P _ xs :- e) = (freeVs e) \\ xs


---------------------------------------------------------------------------

eval :: Context -> Expr -> Expr
eval c e = {-trace (show e ++ "\n") $-} eval' c e

eval' :: Context -> Expr -> Expr
eval' c e = if isVal e then e else eval c $ evalOnce c e

evalOnce :: Context -> Expr -> Expr
evalOnce fs (F name)          = getF fs name
evalOnce _ ((L x e1) :@: e2)  = subst x e2 e1
evalOnce fs (e1 :@: e2)       = (evalOnce fs e1) :@: e2
evalOnce fs (Let x e1 e2)     = subst x (eval fs e1) e2
evalOnce fs (C n es)          = C n (evalOnceList fs es) 
evalOnce fs c@(Case e ps)
    | c@(C name es)        <- e,
      Just (P _ xs :- e'') <- find (isMatch c) ps = substAll xs es e''
    | otherwise               = if isVal e then (error $ (show c) ++ " can't reduce to Constructor") 
                                           else Case (evalOnce fs e) ps

evalOnceList :: Context -> [Expr] -> [Expr]
evalOnceList fs []     = []
evalOnceList fs (e:es) = if isVal e then e : (evalOnceList fs es) else (evalOnce fs e) : es  


---------------------------------------------------------------------------

infixl 5 <:

diving :: Expr -> Expr -> Bool
diving e (C _ es)     = or $ map ((<:) e) es
diving e (L _ el)     = e <: el
diving e (b1 :@: b2)  = (e <: b2) || (e <: b1)
diving e (Case ec pm) = (e <: ec) || (or $ map (\ (_ :- ei) -> e <: ei) pm)
diving _ _            = False

coupling :: Expr -> Expr -> Bool
coupling (C n1 es1) (C n2 es2)       = (n1 == n2) && (length es1 == length es2) && (and $ fmap (uncurry (<:)) $ zip es1 es2) 
coupling (a1 :@: a2) (b1 :@: b2)     = (a2 <: b2) && (coupling a1 b1)
coupling (L _ e1) (L _ e2)           = coupling e1 e2
coupling (Case e1 pm1) (Case e2 pm2) = (coupling e1 e2) && (and $ fmap couplingPM $ zip pm1 pm2)
coupling (V _) (V _)                 = True
coupling e1 e2                       = e1 == e2

couplingPM :: (PatternMatch, PatternMatch) -> Bool
couplingPM (P n1 _ :- e1, P n2 _ :- e2) = (n1 == n2) && (e1 <: e2)

(<:) :: Expr -> Expr -> Bool
(V _) <: (V _) = True
e1    <: e2    = e1 == e2 || diving e1 e2 || coupling e1 e2

---------------------------------------------------------------------------

type Renaming = [(String, String)]

renaming :: Expr -> Expr -> Maybe Renaming
renaming e1 e2 = f $ partition isNothing $ renaming' (e1, e2) where
  f (x:_, _) = Nothing
  f (_, ps) = g gs1 gs2
    where
      gs1 = groupBy (\(a, b) (c, d) -> a == c) $ sortBy h $ nub $ catMaybes ps
      gs2 = groupBy (\(a, b) (c, d) -> b == d) $ sortBy h $ nub $ catMaybes ps
      h (a, b) (c, d) = compare a c
  g xs ys = if all ((== 1) . length) xs && all ((== 1) . length) ys
    then Just (concat xs) else Nothing

getExps :: [PatternMatch] -> [Expr]
getExps ps = map (\(_ :- e) -> e) ps

getPats :: [PatternMatch] -> [Pattern]
getPats ps = map (\(p :- _) -> p) ps

renaming' :: (Expr, Expr) -> [Maybe (String, String)]
renaming' ((V x), (V y))                = if x == y then [] else [Just (x, y)]
renaming' ((C n1 args1), (C n2 args2)) | n1 == n2 = concat $ map renaming' $ zip args1 args2
renaming' ((F n1), (F n2))              = if n1 == n2 then [] else [Nothing]
renaming' (Let v e1 e2, Let v' e1' e2') = error "No renaming for Let supported"  -- renaming' (e1, e1') ++ renaming' (e2, e2' |-| [(v, V v')])
renaming' (a1 :@: b1, a2 :@: b2)        = renaming' (a1, a2) ++ renaming' (b1, b2) 
renaming' (L x e1, L y e2)              = renaming' (e1, e2 |-| [(y, V x)])
renaming' (Case x pats1, Case y pats2) | patsEqual pats1 pats2 = 
    renaming' (x, y) ++ (concat $ map renaming' $ zip (getExps pats1) (getExps pats2))
renaming' _  = [Nothing]

patsEqual :: [PatternMatch] -> [PatternMatch] -> Bool
patsEqual p1 p2 = all (\(P name1 _, P name2 _) -> name1 == name2) $ zip (getPats p1) (getPats p2)

---------------------------------------------------------------------------

type Subst = [(String, Expr)]
type Gen = (Expr, Subst, Subst)
makeGen a b c = (a, b, c)

nameList = ["$" ++ (show x) | x <- [0..]]

deleteP :: Eq a => a -> [(a, b)] -> [(a, b)]
deleteP n xs = filter ((n /=) . fst) xs

infixl 5 |-|

(|-|) :: Expr -> Subst -> Expr
e1 |-| sub = foldl (\e0 (s, e) -> subst s e e0) e1 sub


generalizeList :: [String] -> [(Expr, Expr)] -> ([Gen], [String])
generalizeList names pairs = foldr f ([], names) pairs where
  f (e, e') (acc, ns) = ((gen:acc), ns') where
    (gen, ns') = generalize ns e e'   

trivialGen :: [String] -> Expr -> Expr -> (Gen, [String])
trivialGen (n:ns) e1 e2 = (makeGen (V n) [(n, e1)] [(n, e2)], ns) 


generalizeOnce :: Expr -> Expr -> Gen
generalizeOnce e1 e2 = fst $ generalize nameList e1 e2

generalize :: [String] -> Expr -> Expr -> (Gen, [String])
generalize ns (V a) (V _)         = (makeGen (V a) [] [], ns) 
generalize ns f1@(F n1) f2@(F n2) = if n1 == n2 then (makeGen f1 [] [], ns) else trivialGen ns f1 f2
generalize ns (C name args) (C name' args')
    | name == name'  = (makeGen (C name es) (concat ths1) (concat ths2), ns')
        where
          (gens, ns') = generalizeList ns (zip args args')
          (es, ths1, ths2) = unzip3 gens

generalize ns (e1' :@: e2') (e1'' :@: e2'') 
  = (makeGen (e1 :@: e2) (theta1' ++ theta2') (theta1'' ++ theta2''), ns2) where 
    ((e1, theta1', theta1''), ns1) = generalize ns e1' e1''
    ((e2, theta2', theta2''), ns2) = generalize ns1 e2' e2''

generalize ns (L v1 body1) (L v2 body2) 
  = (makeGen (L freshVName e) th1 th2, ns2) where
    (freshVName:ns1)      = ns
    freshV                = V freshVName
    freshBody1            = body1 |-| [(v1, freshV)]
    freshBody2            = body2 |-| [(v2, freshV)]
    ((e, th1, th2), ns2)  = generalize ns1 freshBody1 freshBody2

generalize ns e1 e2 = trivialGen ns e1 e2

---------------------------------------------------------------------------

data Edge = Label String Graph
          | Option Pattern Graph deriving (Show, Eq)


data Graph = Node Expr [Edge]
           | Fold Expr Renaming deriving (Show, Eq)

---------------------------------------------------------------------------

supercompile :: Context -> Expr -> Graph
supercompile fs e = either superError id $ trySupercompile nameList fs [] (supereval fs e)

superError :: (Expr, Expr) -> Graph
superError (p, e) = error $ "superError: p = " ++ show p ++ "; e = " ++ show e

type Supercomiler = [String] -> Context -> [Expr] -> Expr -> Either (Expr, Expr) Graph

trySupercompile :: Supercomiler
trySupercompile ns fs mem e = case supercompile' ns fs mem e of
    Left ee@(parent, expr) -> if parent == e then superEatLet ns fs mem expr else Left ee
    Right graph            -> Right graph

letEdge :: Expr -> Edge
letEdge l@(Let x e1 _) = Label x $ Node e1 []

superEatLet :: Supercomiler
superEatLet (_:ns) fs mem l@(Let x e1 e2) = (\g -> Node l [letEdge l, Label "in" g]) <$> superEatLet ns fs mem e2
superEatLet ns fs mem e                   = trySupercompile ns fs mem e


showC :: Expr -> String
showC c@(C n es)
    | n == "Z"   = "0"
    | n == "Suc" = show $ e2i c
    | otherwise  = show c

stop :: Expr -> Either (Expr, Expr) Graph
stop e = Right $ Node e []

caseEdge :: Expr -> Edge
caseEdge e = Label "Case" $ Node e []

superBuildGraph :: Supercomiler
superBuildGraph ns fs mem v@(V n) = stop v
superBuildGraph ns fs mem c@(C _ _) | isVal c = stop c
superBuildGraph ns fs mem l@(L _ _) = stop l
superBuildGraph ns fs mem expr = case findFocus expr of
    Just (F n, _)        -> (\g -> Node expr [Label n g]) <$> (trySupercompile ns fs mem $ supereval fs $ evalOnce fs expr)
    Just (Case e' pm, f) -> let lrgs = traverse (\(p :- e) -> ((,) p) <$> trySupercompile ns fs mem (supereval fs $ f e)) pm in --TODO subst
                            case lrgs of
                                Left ee  -> Left ee
                                Right gs -> Right $ Node expr $ (caseEdge e') : ((\(p, g) -> Option p g) <$> gs)
    Nothing             -> stop expr

type Hole = (Expr, Expr -> Expr)

fill :: (Expr -> Expr) -> Hole -> Hole
fill w (e, f) = (e, w . f)

findFocus :: Expr -> Maybe Hole
findFocus (V _)         = Nothing
findFocus (C n es)      = foldl (\b (e, i) -> b <|> (fill (\e' -> let (as, bs) = splitAt i es in C n $ as ++ (e' : (tail bs))) <$> findFocus e)
                                ) Nothing $ zip es [0..]
findFocus (L n e)       = fill (L n) <$> findFocus e
findFocus f@(F n)       = if n `elem` libFun then Nothing else Just (f, id)
findFocus (e1 :@: e2)   = fill (:@: e2) <$> findFocus e1
findFocus c@(Case e pm) = (fill (flip Case pm) <$> findFocus e) <|> Just (c, id)  
findFocus (Let _ _ _)   = error "'Let' shouldn't be in findFocus"  

isVar :: Expr -> Bool
isVar (V _) = True
isVar _     = False

isRenaming :: Subst -> Bool
isRenaming sbst = all (isVar . snd) sbst

genRenaming :: [String] -> Expr -> Expr -> Maybe Renaming
genRenaming ns e1 e2 = let ((eg, th1, th2), ns) = generalize ns e1 e2 in
                       if isRenaming th1 then Just $ (\(x, V y) -> (x, y)) <$> th1 else Nothing

existRenaming :: [Expr] -> Expr -> Maybe (Expr, Renaming)
existRenaming [] e       = Nothing
existRenaming (e':mem) e
    | Just r <- renaming e e' = Just (e', r) 
    | otherwise               = existRenaming mem e


existRenaming2 :: [String] -> [Expr] -> Expr -> Maybe (Expr, Renaming)
existRenaming2 ns [] e       = Nothing
existRenaming2 ns (e':mem) e
    | Just r <- genRenaming ns e e' = Just (e', r) 
    | otherwise               = existRenaming2 ns mem e

existCoupling :: [Expr] -> Expr -> Maybe Expr
existCoupling mem e = find (flip coupling e) mem

notInRenaming :: Renaming -> String -> Bool
notInRenaming [] _          = True
notInRenaming ((_, b):rs) v = v /= b && notInRenaming rs v 

argRenaming :: Expr -> Renaming -> Renaming
argRenaming e r = let vs = filter (notInRenaming r) (freeVs e) in r ++ ((\a -> (a,a)) <$> vs)

supercompile' :: Supercomiler
supercompile' ns fs mem e
    | Just (e', r) <- existRenaming mem e = {-Right $ Node e [Label "-" $ Fold e' $ argRenaming e' r]-}Right  $ Fold e' $ argRenaming e' r
    | Just e'      <- existCoupling mem e, --- e' <:c e
      ((eg, th1, th2), ns') <- generalize ns e e', -- e п e'
      not (isVar eg)                      = if isRenaming th2 -- eg == e' с точностью до переименования
                                                then superEatLet ns fs mem $ makeLetIn eg th1  -- Bottom Generalization
                                                else Left (e', makeLetIn eg th2)               -- Up Generalization
    | otherwise                           = superBuildGraph ns fs (e:mem) e


supereval :: Context -> Expr -> Expr
supereval fs e = maybe e (supereval fs) $ supereval' fs e

supereval' :: Context -> Expr -> Maybe Expr
supereval' fs e@((L _ _) :@: _)  = Just $ evalOnce fs e 
supereval' fs (e1 :@: e2)        = (\e' -> e' :@: e2) <$> supereval' fs e1
supereval' fs c@(C n es)         = (C n) <$> superevalList fs es
supereval' fs e@(Case (C _ _) _) = Just $ evalOnce fs e
supereval' fs (Case e pm)        = (\e' -> Case e' pm) <$> supereval' fs e  
supereval' fs f@(F n)            = Nothing 
supereval' fs e                  = Nothing

superevalList :: Context -> [Expr] -> Maybe [Expr]
superevalList fs []     = Nothing
superevalList fs (e:es) = if isVal e then (e :) <$> superevalList fs es
                                     else (: es) <$> supereval' fs e

makeLetIn :: Expr -> Subst -> Expr
makeLetIn e []           = e
makeLetIn e ((n, e'):ss) = Let n e' $ makeLetIn e ss

---------------------------------------------------------------------------

isNum :: Expr -> Bool
isNum (C "Z" xs)   = True
isNum (C "Suc" xs) = isNum $ head xs
isNum _            = False

getNode :: Graph -> String
getNode (Node e _) = "\"" ++ (show e) ++ "\""
getNode (Fold e _) = "\"" ++ (show e) ++ "\""

label :: String -> Graph -> String
label s (Fold _ r) = s ++ " -> Fold [" ++ (intercalate " " ((\(a, b) -> "(" ++ a ++ " -> " ++ b ++ ")") <$> r)) ++ "]"
label s _          = s

getEdge :: Edge -> (String, Graph)
getEdge (Label s g) = (s, g)
getEdge (Option p g) = (show p, g)

showGraph :: Graph -> String
showGraph n@(Node e edges) = concat $ (\edg -> let (s, g) = getEdge edg in getNode n ++ " -> " ++  getNode g  ++ " [label=\"" ++ label s g ++ "\"];\n" ++ showGraph g) <$> edges 
showGraph _ = ""

renderDot graph = "digraph G {\n" ++ showGraph graph ++ "}"

-- data Edge = Label String Graph deriving (Show, Eq)


-- data Graph = Node Expr [Edge]
--            | Fold Expr Renaming

nextNode :: Edge -> Graph
nextNode (Label _ g) = g
nextNode (Option _ g) = g

getOption :: Edge -> Pattern
getOption (Option p _) = p

getExpr :: Graph -> Expr
getExpr (Node e _) = e
getExpr (Fold e _) = e

findFoldes :: Graph -> [(Expr, Renaming)]
findFoldes (Node _ egs) = concat $ (findFoldes . nextNode) <$> egs
findFoldes (Fold e r)   = [(e, r)]

type FstSnd = (String, String) -> String

generateCode :: Graph -> (Expr, Context)
generateCode g@(Node e _) = let (expr, context) = callGen g in (genLamS (freeVs expr) expr, context) where
                    foldes :: [(Expr, (Renaming, Expr))]
                    foldes = (\((e, r), f) -> (,) e (r, F f)) <$> (zip (findFoldes g) ["#" ++ (show x) | x <-[1..]])
                    
                    callGen :: Graph -> (Expr, Context)
                    callGen g@(Node e egs) = maybe (gen g) (genFun g) $ lookup e foldes
                    callGen g              = gen g
                    
                    gen :: Graph -> (Expr, Context)
                    gen (Node e egs) = if null egs then (e, []) else
                                       let (Label n g1) = head egs in
                                       if head n == '$' then let (el, c) = callGen (nextNode $ egs !! 1) in (Let n (getExpr g1) el, c)
                                       else if n == "Case" then (let (ps, (es, ctxs)) = (getOption <$> tail egs, unzip $ (callGen . nextNode) <$> tail egs)
                                                                 in (Case (getExpr g1) ((\(p', e') -> p' :- e') <$> zip ps es), concat ctxs))
                                       else callGen g1 
                    gen (Fold e _)   = (call fst e, [])
                    
                    call :: FstSnd -> Expr -> Expr
                    call f e = callF f $ fromJust $ lookup e foldes

                    callF :: FstSnd -> (Renaming, Expr) -> Expr
                    callF f fld = uncurry genApp fld f
                    
                    genApp :: Renaming -> Expr -> FstSnd -> Expr
                    genApp [] e _     = e
                    genApp (r:rs) e f = genApp rs (e :@: (V $ f r)) f  
                    
                    genLam :: Renaming -> Expr -> Expr
                    genLam rs e = genLamS (snd <$> rs) e

                    genLamS :: [String] -> Expr -> Expr
                    genLamS [] e     = e
                    genLamS (x:xs) e = L x $ genLamS xs e
                    
                    genFun :: Graph -> (Renaming, Expr) -> (Expr, Context)
                    genFun g@(Node e _) f@(r, F n) = let (fe, ctx) = gen g in (callF snd f, (n, genLam r fe) : ctx)
---------------------------------------------------------------------------


i2e :: Int -> Expr 
i2e n
    | n == 0    = C "Z" []
    | otherwise = C "Suc" [i2e (n - 1)]

e2i :: Expr -> Int
e2i e
    | C n es <- e = if n == "Z" then 0 else if n == "Suc" then 1 + e2i (head es) else error "it is not int"
    | otherwise   = error "it is not Cuctor of int"


fplus = L "n" $ L "m" $ Case (V "n") [
        P "Suc" ["x"]   :- C "Suc" [F "+" :@: V "x" :@: V "m"],
        P "Z" []        :- V "m"
    ]

fmult = L "n" $ L "m" $ Case (V "n") [
        P "Suc" ["x"]   :- F "+" :@: V "m" :@: (F "*" :@: V "x" :@: V "m"),
        P "Z" []        :- C "Z" []
    ]

fsquare = L "n" $ F "*" :@: V "n" :@: V "n"

fgreater = L "n" $ L "m" $ Case (V "n") [
        P "Z"   []    :- C "Fls" [],
        P "Suc" ["x"] :- Case (V "m") [
                P "Z"  []     :- C "Tru" [],
                P "Suc" ["y"] :- F ">" :@: V "x" :@: V "y" 
            ]
    ]

fsum = L "xs" $ L "a" $ Case (V "xs") [
        P "Nil"  []          :- V "a",
        P "Cons" ["x", "xs"] :- F "sum" :@: V "xs" :@: (F "+" :@: V "x" :@: V "a")
    ]

fsquares = L "xs" $ Case (V "xs") [
        P "Nil"  []          :- C "Nil" [],
        P "Cons" ["x", "xs"] :- C "Cons" [F "^2" :@: V "x", F "squares" :@: V "xs"]
    ]

fupto = L "n" $ L "m" $ Case (F ">" :@: V "n" :@: V "m") [
        P "Tru" [] :- C "Nil" [],
        P "Fls" [] :- C "Cons" [V "n", F "upto" :@: (F "+" :@: (i2e 1) :@: V "n") :@: V "m"]
    ]

fcompare = L "a" $ L "b" $ Case (V "a") [
        P "0" [] :- Case (V "b") [
                P "0" [] :- C "Tru" [],
                P "1" [] :- C "Fls" []
            ],
        P "1" [] :- Case (V "b") [
                P "0" [] :- C "Fls" [],
                P "1" [] :- C "Tru" []
            ]
    ]

fmatch = L "p" $ L "s" $ F "loop" :@: V "p" :@: V "s" :@: V "p" :@: V "s"

floop = L "pp" $ L "ss" $ L "op" $ L "os" $ Case (V "pp") [
        P "Nil" []           :- C "Tru" [],
        P "Cons" ["p", "pz"] :- Case (V "ss") [
                P "Nil"  []          :- C "Fls" [],
                P "Cons" ["s", "sz"] :- Case (F "==" :@: V "p" :@: V "s") [
                        P "Tru" [] :- F "loop" :@: V "pz" :@: V "sz" :@: V "op" :@: V "os",
                        P "Fls" [] :- F "next" :@: V "op" :@: V "os"
                    ]
            ]
    ]

fnext = L "op" $ L "ss" $ Case (V "ss") [
        P "Nil" []           :- C "Fls" [],
        P "Cons" ["s", "sz"] :- F "loop" :@: V "op" :@: V "sz" :@: V "op" :@: V "sz" 
    ]


libFun = ["+", "*", "^2", ">", "=="]

functions = [("+", fplus), ("*", fmult), ("^2", fsquare), (">", fgreater), ("==", fcompare),
             ("sum", fsum), ("squares", fsquares), ("upto", fupto),
             ("match", fmatch), ("loop", floop), ("next", fnext)]

list2e :: [Int] -> Expr
list2e []     = C "Nil" []
list2e (x:xs) = C "Cons" [i2e x, list2e xs]

str2e :: String -> Expr
str2e ""     = C "Nil" []
str2e (x:xs) = C "Cons" [C (x:"") [], str2e xs]

example n = F "sum" :@: (F "squares" :@: (F "upto" :@: i2e 1 :@: i2e n)) :@: i2e 0

example2 = F "sum" :@: (F "squares" :@: (F "upto" :@: i2e 1 :@: V "n")) :@: i2e 0

checkEval n = eval functions $ example n

check = supercompile functions example2

super n = let (e, c) = generateCode check in eval (functions ++ c) (e :@: i2e n)

toFile = writeFile "file.txt" $ renderDot check


------------------------------------------------------------------------------

match s = eval functions $ F "match" :@: str2e "010" :@: str2e s

superMatch = supercompile functions $ F "match" :@: str2e "010" :@: V "str"

writeMatch = writeFile "match.txt" $ renderDot superMatch

smatch str = let (e, c) = generateCode superMatch in eval (functions ++ c) (e :@: str2e str)
