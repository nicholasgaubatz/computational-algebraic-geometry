                                                                                                           2   2   2   2   2   2
HashTable{AOTideal => ideal (y y y y y  - y y y y y  - y y y y y  + y y y y y  + y y y y y  - y y y y y , y , y , y , y , y , y )}
                              1 2 3 4 5    1 2 3 4 6    1 2 3 5 6    1 2 4 5 6    1 3 4 5 6    2 3 4 5 6   1   2   3   4   5   6
                                2   2   2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y y y y y )
                                6   5   4   3   2   1   1 2 3 4 5
          graph => {set {0, 3}, set {1, 3}, set {0, 4}, set {1, 5}, set {2, 4}, set {2, 5}}
                                 2      3      4     5
          hSeries => 1 + 6T + 15T  + 20T  + 15T  + 5T
          hyperplanes => {a - d, b - d, a - e, b - f, c - e, c - f}
          numVariables => 6
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_6]
AOTideal = ideal map(R^1,R^{{-5}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_2*y_3*y_4*y_5-y_1*y_2*y_3*y_4*y_6-y_1*y_2*y_3*y_5*y_6+y_1*y_2*y_4*y_5*y_6+y_1*y_3*y_4*y_5*y_6-y_2*y_3*y_4*y_5*y_6, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-5}},{{y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_1*y_2*y_3*y_4*y_5}})
G = graph {set {0, 3}, set {1, 3}, set {0, 4}, set {1, 5}, set {2, 4}, set {2, 5}}
