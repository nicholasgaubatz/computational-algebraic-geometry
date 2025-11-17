                                                                 2   2   2   2   2   2
HashTable{AOTideal => ideal (y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y )    }
                              1 2 3    1 2 4    1 3 4    2 3 4   1   2   3   4   5   6
                                2   2   2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y y y )
                                6   5   4   3   2   1   1 2 3
          graph => {set {0, 5}, set {1, 5}, set {0, 6}, set {1, 6}, set {2, 6}, set {3, 6}}
                                 2      3      4     5
          hSeries => 1 + 6T + 15T  + 19T  + 12T  + 3T
          hyperplanes => {a - f, b - f, a - g, b - g, c - g, d - g}
          numVariables => 6
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_6]
AOTideal = ideal map(R^1,R^{{-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_2*y_3-y_1*y_2*y_4-y_1*y_3*y_4+y_2*y_3*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_1*y_2*y_3}})
G = graph {set {0, 5}, set {1, 5}, set {0, 6}, set {1, 6}, set {2, 6}, set {3, 6}}
