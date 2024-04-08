#![allow(warnings)]
use ilog::IntLog;
use prime_checker::get_primes;
use std::collections::HashMap;
use std::time::{Duration, Instant};
use rand::Rng;
use itertools::Itertools;
use num_bigint::{BigUint, BigInt, Sign, ToBigInt, ToBigUint};
use num_traits::ops::euclid::Euclid;
use num_traits::cast::ToPrimitive;
use polynomen::{poly,Poly};
use plotters::prelude::*;
use std::fs::{File, OpenOptions};
use std::io::prelude::*;
use struson::writer::*;


fn random_poly_alpha(d:u32, q:u128, m:u32) -> (HashMap<Vec<u32>,i128>,Vec<i128>) { // This function generates a random polynomial of degree d, with m variables and in Z_q and also a value in which the polynomial can be evaluated
    let mut f: HashMap<Vec<u32>, i128> = HashMap::with_capacity(d.pow(m) as usize);
    let mut alpha: Vec<i128> = Vec::with_capacity(m as usize);
    let mut i: u32 = 0;
    for pows in (0..m).map(|i| 0..d+1).multi_cartesian_product() {
        let coef: i128 = rand::thread_rng().gen_range(0..q) as i128;
        f.insert(pows,coef);
        if (i < m) {
            let alpha_i: i128 = rand::thread_rng().gen_range(0..q) as i128;
            alpha.push(alpha_i);
            i += 1;
        }   
    }
    (f,alpha)
}


fn naive_eval(x:&Vec<i128>, f:&HashMap<Vec<u32>,i128>, q:u128) -> i128 { // This function evaluates the polynomial f in x using the naive algorithm (just to test)
    let mut res: i128 = 0;
    let l: usize = x.len();
    for i in f {
        let mut term: i128 = 1;
        for j in 0..l {
            term *= x[j].pow(i.0[j]);
        }
        res += (term * i.1)%(q as i128);
    }
    res%(q as i128)
}


fn add_head(h:i128, x:&Vec<i128>) -> Vec<i128> { // This is an auxiliary function to add a head to a vec
    let l: usize = x.len()+1;
    let mut hx: Vec<i128> = Vec::with_capacity(l);
    hx.push(h);
    for i in x {
        hx.push(*i);
    }
    hx
}


fn translate_into_R(f:&HashMap<Vec<u32>,i128>) -> Poly<f64> { // This is an auxiliary function to translate types
    let mut f_coeffs: Vec<f64> = Vec::new();
    for i in 0..f.len() {
        f_coeffs.push(f.get(&vec![i as u32]).unwrap_or(&0).clone() as f64);
    }
    let f_hat: Poly<f64> = Poly::new_from_coeffs(&f_coeffs);
    f_hat
}


fn translate_into_HashMap(e:&Vec<i128>) -> HashMap<Vec<i128>,i128> { // This is an auxiliary function to translate types
    let mut hm: HashMap<Vec<i128>,i128> = HashMap::with_capacity(e.len());
    for i in 0..e.len() {
        hm.insert(vec![i as i128],e[i]);
    }
    hm
}


fn heq_pow_2(p_i:u128) -> (u128,u32) { // This function returns the first power of 2 above p_i
    let mut r: u128 = 1;
    let mut k: u32 = 0;
    while r < p_i {
        r *= 2;
        k += 1;
    }
    (r,k)
}


fn index_of_M_i_j(i:u32, j:u128, n:u128) -> usize { // This function returns the index of the vector where M_i_j is allocated
    let mut index: usize = j as usize;
    let mut pow: u128 = n;
    for x in 0..i {
        index += pow as usize;
        pow /= 2;
    }
    index
}


fn build_tree(p_i:u128) -> (Vec<Poly<f64>>,u128,u32) { // Algorithm 10.3 [MCA]
    let (r,k): (u128,u32) = heq_pow_2(p_i);
    let mut new_index: u128 = 0;
    let mut js: u128 = r;
    let mut tree: Vec<Poly<f64>> = Vec::with_capacity(2*r as usize); // The order in which nodes are inserted has a pattern (algorithm index_of_M_i_j gives it explicitly) so we don't really need a tree to store the polynomials
    for i in 0..k+1 {
        for j in 0..js {
            if (i == 0) {
                tree.push(poly![-(j as f64), 1.]);
            }
            else {
                let index0: usize = (new_index+2*j) as usize;
                let index1: usize = index0+1;
                let poly: Poly<f64> = (tree[index0].clone()).mul_fft(tree[index1].clone());
                let round_poly: Poly<f64> = Poly::new_from_coeffs_iter(poly.coeffs().iter().map(|c| c.round() % p_i as f64));
                tree.push(round_poly);
            }
        }
        js /= 2;
        if (i != 0) {new_index += 2_u128.pow(k-i+1);}
    }
    (tree,r,k)
}


fn down_tree(f:&Poly<f64>, n:u128, i:u32, j:u128, index:usize, tree:&Vec<Poly<f64>>, r:usize, p_i:u128) -> Vec<i128> { // Algorithm 10.5 [MCA] (Important: f has to have degree lower than n (which is the lowest power of 2 above p_i))
    if (n == 1) {vec![(((f.leading_coeff()%p_i as f64)+p_i as f64) as u128 % p_i) as i128]}
    else {
        let index_ls: usize = index-r+j as usize;
        let index_rs: usize = index_ls+1;
        let r_0: Poly<f64> = f % &tree[index_ls];
        let r_1: Poly<f64> = f % &tree[index_rs];
        let mut v_0: Vec<i128> = down_tree(&r_0, n/2, i-1, 2*j, index_ls, tree, 2*r, p_i);
        let v_1: Vec<i128> = down_tree(&r_1, n/2, i-1, 2*j+1, index_rs, tree, 2*r, p_i);
        v_0.extend(v_1);
        v_0.truncate(p_i as usize);
        v_0
    }
}


fn multipoint_univariate_evaluation(f:&HashMap<Vec<u32>,i128>, p_i:u128) -> Vec<i128> { // Algorithm 10.7 [MCA]: Computes f(Z_p_i) efficiently
    let f_hat: Poly<f64> = translate_into_R(f);
    let (tree,n,k): (Vec<Poly<f64>>,u128,u32) = build_tree(p_i);
    let top_index: usize = 2*(n as usize)-2;
    down_tree(&f_hat, n, k, 0, top_index, &tree, 2, p_i)
}


fn reduce_vars(f:&HashMap<Vec<u32>,i128>, i:u128) -> HashMap<Vec<u32>,i128> { // This function returns f_i for a given i where f(X_0,...,X_{m-1}) = sum_i{X^i_{0}*f_i(X_1,...,X_{m-1})}
    let mut f_i:HashMap<Vec<u32>,i128> = HashMap::with_capacity(f.len() as usize);
    for (pows,coef) in f {
        if (pows[0] == i as u32) {f_i.insert(pows[1..].to_vec(),*coef);}
    }
    f_i
}


fn multipoint_multivariate_evaluation(f:&HashMap<Vec<u32>,i128>, p_i:u128, m:u32) -> HashMap<Vec<i128>,i128> { // This function evaluates the polynomial f using multivariate FFT
    let mut T: HashMap<Vec<i128>,i128> = HashMap::new();
    if (m == 1) {T = translate_into_HashMap(&multipoint_univariate_evaluation(f,p_i));}
    else {
        let mut T_is: Vec<HashMap<Vec<i128>,i128>> = Vec::with_capacity(p_i as usize);
        for i in 0..p_i {
            let f_i: HashMap<Vec<u32>,i128> = reduce_vars(&f,i);
            T_is.push(multipoint_multivariate_evaluation(&f_i,p_i,m-1));
        }
        for beta in (0..m-1).map(|i| 0..p_i as i128).multi_cartesian_product() {
            let mut UV_f_beta: HashMap<Vec<u32>,i128> = HashMap::with_capacity(p_i as usize);
            for i in 0..p_i {
                UV_f_beta.insert(vec![i as u32],*(T_is[i as usize]).get(&beta).unwrap());
            }
            let mut alpha0: i128 = 0;
            for eval_alpha in multipoint_univariate_evaluation(&UV_f_beta, p_i) {
                let alpha: Vec<i128> = add_head(alpha0,&beta);
                T.insert(alpha,eval_alpha);
                alpha0 += 1;
            }
        }
    }
    T
}


fn module_Xp_X(f:&HashMap<Vec<u32>,i128>, p:u128, m:u32) -> HashMap<Vec<u32>,i128> { // This function reduces the polynomial f modulo ((X_j)^p - X_j) for every j in {0,...,m-1}
    let mut red_f: HashMap<Vec<u32>,i128> = HashMap::with_capacity(f.len());
    for mon in f {
        let mut new_pows: Vec<u32> = Vec::with_capacity(m as usize);
        for j in 0..m {
            let i_j: u32 = mon.0[j as usize];
            if ((i_j as u128) < p) {new_pows.push(i_j);}
            else {
                let n_j: u32 = (((i_j as u128 - p) as f64 / (p-1) as f64)+1.0).floor() as u32;
                let new_pow: u32 = i_j + n_j - n_j * (p as u32);
                new_pows.push(new_pow);
            }
        }
        if (red_f.contains_key(&new_pows)) {
            let coeff: i128 = (red_f.get(&new_pows).unwrap() + mon.1) % (p as i128);
            if (coeff == 0) {red_f.remove(&new_pows);}
            else {red_f.insert(new_pows,coeff);}
        }
        else {red_f.insert(new_pows,*mon.1);}
    }
    red_f
}


fn FFT_multipoint_eval(f:&HashMap<Vec<u32>,i128>, p_i:u128, m:u32) -> HashMap<Vec<i128>,i128> { // This function implements [KU08, Theorem 4.1] (reduces f and evaluates it on all (Z_p_i)^m using FFT based multipoint evaluation)
    let red_f: HashMap<Vec<u32>,i128> = module_Xp_X(f,p_i,m);
    let T_i: HashMap<Vec<i128>,i128> = multipoint_multivariate_evaluation(&red_f,p_i,m);
    T_i
}


fn lift(f:&HashMap<Vec<u32>,i128>, q:u128) -> HashMap<Vec<u32>,i128> { // This function "lifts" the polynomial f in Z_q to Z (sets every coefficient of f to its [0,q-1] value in Z_q)
    let mut lift_f: HashMap<Vec<u32>,i128> = HashMap::with_capacity(f.len() as usize);
    for (pows,coeff) in f {
        let new_coeff: i128 = coeff.rem_euclid(&(q as i128));
        lift_f.insert(pows.clone(),new_coeff);
    }
    lift_f
}


fn egcd(a:&BigInt, b:&BigInt) -> (BigInt,BigInt,BigInt) { // This is an auxiliary function for the CRT algorithm
    if (*a == 0.to_bigint().unwrap()) {(b.clone(), 0.to_bigint().unwrap(), 1.to_bigint().unwrap())} 
    else {
        let (g,x,y):(BigInt,BigInt,BigInt) = egcd(&(b%a),a);
        (g, y-(b/a)*&x, x)
    }
}


fn mod_inv(x:&BigInt, n:&BigInt) -> Option<BigInt> { // This is an auxiliary function for the CRT algorithm
    let (g, x,_) = egcd(&x,&n);
    if (g == 1.to_bigint().unwrap()) {Some(x.rem_euclid(&n))} 
    else {None}
}


fn Chinese_Remainder_Theorem(residues:&Vec<BigInt>, modules:Vec<BigUint>) -> BigInt { // This function solves a system of modular equations given the modules and the residues using CRT
    let prod: BigUint = modules.iter().product();
    let mut sum: BigInt = BigInt::new(Sign::Plus, vec![0]);
    for (residue,module) in residues.iter().zip(modules) {
        let p: BigInt = BigInt::from_biguint(Sign::Plus,&prod/&module);
        sum += residue * mod_inv(&p,&BigInt::from_biguint(Sign::Plus,module)).unwrap() * p;
    }
    sum%(BigInt::from_biguint(Sign::Plus,prod))
}


fn preprocessingA3(d:u32, q:u128, m:u32, f:&HashMap<Vec<u32>,i128>) -> (Vec<u128>,Vec<HashMap<Vec<i128>,i128>>) { // This function returns the preprocessed data structure that allows fast evaluation of multivariate polynomials
    let M: u128 = d.pow(m) as u128 * q.pow(m*(d-1)+1);
    let bound: u128 = 16*IntLog::log2(M) as u128;
    let mut DS: (Vec<u128>,Vec<HashMap<Vec<i128>,i128>>) = (get_primes(bound as u64).iter().map(|&x| x as u128).collect(),Vec::new());
    let lift_f: HashMap<Vec<u32>,i128> = lift(f,q);
    for p_i in &DS.0 {
        let f_i: HashMap<Vec<u32>,i128> = lift(&lift_f,*p_i);
        let T_i: HashMap<Vec<i128>,i128> = FFT_multipoint_eval(&f_i,*p_i,m);
        DS.1.push(T_i);
    }
    DS
}


fn fast_evalA3(alpha:&Vec<i128>, DS:&(Vec<u128>,Vec<HashMap<Vec<i128>,i128>>), q:u128) -> (i128,Duration) { // This function evaluates multivariate polynomials fast by using the data structure returned by preprocessingA3
    let t0_in: Instant = Instant::now();
    let mut i: u32 = 0;
    let mut residues: Vec<i128> = Vec::with_capacity(DS.0.len() as usize);
    let modules: &Vec<u128> = &DS.0;
    for p_i in modules {
        let alpha_i: Vec<i128> = alpha.iter().map(|x| x.rem_euclid(&(*p_i as i128))).collect();
        let f_alpha_i: i128 = *(DS.1[i as usize].get(&alpha_i).unwrap());
        residues.push(f_alpha_i);
        i += 1;
    }
    let z: i128 = (Chinese_Remainder_Theorem(&residues.iter().map(|x| x.to_bigint().unwrap()).collect(),modules.iter().map(|x| x.to_biguint().unwrap()).collect())%q).to_i128().unwrap();
    let time_in: Duration = t0_in.elapsed();
    (z,time_in)
}


fn test(d:u32, m:u32, q:u128) -> (Duration,Duration,Duration) { // This function compares the outcome of the fast algorithm with the naive algorithm
    // Initialization of random poly f and alpha with: degree d, number of variables m and ring Z_q
    let (f,alpha): (HashMap<Vec<u32>,i128>, Vec<i128>) = random_poly_alpha(d,q,m);
    // Preprocessing data structure 
    let t0_preprocessing: Instant = Instant::now();
    let DS: (Vec<u128>, Vec<HashMap<Vec<i128>,i128>>) = preprocessingA3(d,q,m,&f);
    let time_preprocessing: Duration = t0_preprocessing.elapsed();
    // Evaluations
    //let t0_fe: Instant = Instant::now();
    let (fe,time_fe): (i128,Duration) = fast_evalA3(&alpha,&DS,q);
    //let time_fe: Duration = t0_fe.elapsed();
    
    let t0_ne: Instant = Instant::now();
    let ne: i128 = naive_eval(&alpha,&f,q);
    let time_ne: Duration = t0_ne.elapsed();
    (time_fe,time_ne,time_preprocessing)
}


fn plotter() {
    let q: u128 = 5;
    let m: u32 = 3;
    let mut fe_times: HashMap<u32,u128> = HashMap::with_capacity(11);
    let mut ne_times: HashMap<u32,u128> = HashMap::with_capacity(11);
    let mut prep_times: HashMap<u32,u128> = HashMap::with_capacity(11);
    let mut x_values: [f64;11] = [0.,1.,2.,3.,4.,5.,6.,7.,8.,9.,10.];
    let mut max_y_e: f64 = 0.;
    let mut max_y_p: f64 = 0.;
    for d in 0..11 {
        //let time: (u128,u128,u128) = test(d,m,q);
        let time: (u128,u128,u128) = (0,10,20);
        fe_times.insert(d,time.0);
        ne_times.insert(d,time.1);
        prep_times.insert(d,time.2);
        max_y_e = max_y_e.max(time.0 as f64).max(time.1 as f64);
        max_y_p = max_y_p.max(time.2 as f64);
    }

    let drawing_area1 = BitMapBackend::new("test1.png", (1080, 810)).into_drawing_area();
    drawing_area1.fill(&WHITE).unwrap();
    let mut chart_builder1 = ChartBuilder::on(&drawing_area1);
    chart_builder1.margin(20).set_left_and_bottom_label_area_size(20);
    let mut chart_context1 = chart_builder1.caption("Preprocessing fixed q = 5 and m = 3", ("sans-serif", 30)).x_label_area_size(40).y_label_area_size(40).build_cartesian_2d(0.0..10.0, 0.0..max_y_p+10.0).unwrap();
    chart_context1.configure_mesh().x_desc("Degree d").y_desc("Time in s").disable_mesh().x_label_formatter(&|x:&f64| format!("{:.0}", x)).draw().unwrap();
    chart_context1.draw_series(LineSeries::new(x_values.map(|x| (x, *prep_times.get(&(x.round() as u32)).unwrap() as f64)), BLUE)).unwrap();

    let drawing_area2 = BitMapBackend::new("test2.png", (1080, 810)).into_drawing_area();
    drawing_area2.fill(&WHITE).unwrap();
    let mut chart_builder2 = ChartBuilder::on(&drawing_area2);
    chart_builder2.margin(20).set_left_and_bottom_label_area_size(20);
    let mut chart_context2 = chart_builder2.caption("Evaluations fixed q = 5 and m = 3", ("sans-serif", 30)).x_label_area_size(40).y_label_area_size(40).build_cartesian_2d(0.0..10.0, 0.0..max_y_e+10.0).unwrap();
    chart_context2.configure_mesh().x_desc("Degree d").y_desc("Time in ms").disable_mesh().x_label_formatter(&|x:&f64| format!("{:.0}", x)).draw().unwrap();
    chart_context2.draw_series(LineSeries::new(x_values.map(|x| (x, *fe_times.get(&(x.round() as u32)).unwrap() as f64)), BLUE)).unwrap().label("KU08 evaluation").legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], BLUE));
    chart_context2.draw_series(LineSeries::new(x_values.map(|x| (x, *ne_times.get(&(x.round() as u32)).unwrap() as f64)), RED)).unwrap().label("Naive evaluation").legend(|(x, y)| PathElement::new(vec![(x, y), (x + 20, y)], RED));
    chart_context2.configure_series_labels().position(SeriesLabelPosition::LowerRight).border_style(BLACK).draw().unwrap();
}


fn main() -> std::io::Result<()> {
    let qs: Vec<u128> = vec![2,3,5,7,11];
    let ms: Vec<u32> = vec![1,2,3,4,5];
    let ds: Vec<u32> = vec![1,2,3,4,5];
    let mut writer: File = OpenOptions::new().append(true).read(true).open("test.json")?;
    writer.write(b"[\n");
    let mut json_writer_settings: WriterSettings = WriterSettings::default();
    json_writer_settings.multi_top_level_value_separator = Some(String::from(",\n"));
    let mut json_writer: JsonStreamWriter<&mut File> = JsonStreamWriter::new_custom(&mut writer,json_writer_settings);
    for d in ds {
        for m in ms.iter() {
            for q in qs.iter() {
                json_writer.begin_object()?;
                
                json_writer.name("d")?;
                json_writer.number_value(d)?;

                json_writer.name("m")?;
                json_writer.number_value(*m)?;

                json_writer.name("q")?;
                json_writer.number_value(*q)?;
            
                json_writer.end_object()?;
            }
        }
    }
    json_writer.finish_document()?;
    writer.write(b"\n]");
    Ok(())
}