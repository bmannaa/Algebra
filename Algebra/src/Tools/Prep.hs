module Tools.Prep where

prep :: String -> String
prep = addTrivCoeff . addTrivPower . addInitSign . filter (/=' ') 

addInitSign :: String -> String
addInitSign [] = []
addInitSign (x:xs) | x /='+' && x /='-' = '+':x:xs
                   | otherwise          = x:xs


addTrivPower :: String -> String
addtrivPower [] = []
addTrivPower [x] | (x == 'X' || x == 'Y') = x : '^' : '1' : []
                 | otherwise = [x]
addTrivPower (a:b:xs) | (a == 'X' || a == 'Y') && (b /= '^') = a : '^' : '1' : addTrivPower (b:xs)
                      | otherwise = a : addTrivPower (b:xs)

addTrivCoeff :: String -> String
addTrivCoeff [] = []
addTrivCoeff [x] = [x]
addTrivCoeff (a:b:xs) | (a == '+' || a == '-') && (b == 'X' || b == 'Y') = a:'1':b: addTrivCoeff xs
                      | otherwise = a : addTrivCoeff (b:xs)
