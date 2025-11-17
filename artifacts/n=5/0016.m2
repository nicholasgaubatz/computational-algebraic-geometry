                                                                                                                                       2   2   2   2   2   2
HashTable{AOTideal => ideal (y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y )}
                              2 3 5    2 3 6    2 5 6    3 5 6   1 3 4    1 3 6    1 4 6    3 4 6   1 2 4    1 2 5    1 4 5    2 4 5   1   2   3   4   5   6
                                2   2   2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y y y , y y y , y y y )
                                6   5   4   3   2   1   2 3 5   1 3 4   1 2 4
          graph => {set {0, 3}, set {1, 3}, set {2, 3}, set {0, 4}, set {1, 4}, set {2, 4}}
                                 2      3     4
          hSeries => 1 + 6T + 15T  + 17T  + 7T
          hyperplanes => {a - d, b - d, c - d, a - e, b - e, c - e}
          numVariables => 6
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_6]
AOTideal = ideal map(R^1,R^{{-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_2*y_3*y_5-y_2*y_3*y_6-y_2*y_5*y_6+y_3*y_5*y_6, y_1*y_3*y_4-y_1*y_3*y_6-y_1*y_4*y_6+y_3*y_4*y_6, y_1*y_2*y_4-y_1*y_2*y_5-y_1*y_4*y_5+y_2*y_4*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}},{{y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_2*y_3*y_5, y_1*y_3*y_4, y_1*y_2*y_4}})
G = graph {set {0, 3}, set {1, 3}, set {2, 3}, set {0, 4}, set {1, 4}, set {2, 4}}
