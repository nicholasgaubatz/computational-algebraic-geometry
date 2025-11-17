                                                                 2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y y  + y y y  - y y y  - y y y , y , y , y , y , y , y , y )            }
                              1 3 4    1 3 6    1 4 6    3 4 6   1   2   3   4   5   6   7
                                2   2   2   2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y , y , y , y y y )
                                7   6   5   4   3   2   1   1 3 4
          graph => {set {0, 4}, set {1, 4}, set {4, 6}, set {0, 5}, set {2, 5}, set {5, 6}, set {3, 6}}
                                 2      3      4      5     6
          hSeries => 1 + 7T + 21T  + 34T  + 31T  + 15T  + 3T
          hyperplanes => {a - e, b - e, e - g, a - f, c - f, f - g, d - g}
          numVariables => 7
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_7]
AOTideal = ideal map(R^1,R^{{-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_3*y_4+y_1*y_3*y_6-y_1*y_4*y_6-y_3*y_4*y_6, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}},{{y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_2^2, y_1^2, y_1*y_3*y_4}})
G = graph {set {0, 4}, set {1, 4}, set {4, 6}, set {0, 5}, set {2, 5}, set {5, 6}, set {3, 6}}
