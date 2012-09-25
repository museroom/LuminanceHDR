/**
 * This file is a part of Luminance HDR package
 * ---------------------------------------------------------------------- 
 * Copyright (C) 2006,2007 Giuseppe Rota
 * 
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 * ---------------------------------------------------------------------- 
 *
 * @author Giuseppe Rota <grota@users.sourceforge.net>
 * Improvements, bugfixing
 * @author Franco Comida <fcomida@users.sourceforge.net>
 *
 */

#include <QDebug>

#include <QApplication>
#include <QFileInfo>
#include <QFile>
#include <QColor>

#include <algorithm>
#include <cmath>

#include <gsl/gsl_matrix.h>
#include <gsl/gsl_linalg.h>
#include <gsl/gsl_blas.h>

#include "Libpfs/domio.h"
#include "Fileformat/pfstiff.h"
#include "Fileformat/pfsouthdrimage.h"
#include "Filter/pfscut.h"
#include "Exif/ExifOperations.h"
#include "Threads/HdrInputLoader.h"
#include "mtb_alignment.h"
#include "HdrCreationManager.h"
#include "arch/math.h"
#include "Common/msec_timer.h"
#include "Viewers/Histogram.h"

namespace
{
void rgb2hsl(float r, float g, float b, float *h, float *s, float *l)
{
    float v, m, vm, r2, g2, b2;
    *h = 0.0f;
    *s = 0.0f;
    *l = 0.0f;
    v = std::max(r, g);
    v = std::max(v, b);
    m = std::min(r, g);
    m = std::min(m, b);
    *l = (m + v) * 0.5f;
    if (*l <= 0.0f)
        return;
    vm = v - m;
    *s = vm;
    if (*s >= 0.0f)
        *s /= (*l <= 0.5f) ? (v + m) : (2.0f - v - m);
    else return;
    r2 = (v - r) / vm;
    g2 = (v - g) / vm;
    b2 = (v - b) / vm;
    if (r == v)
        *h = (g == m ? 5.0f + b2 : 1.0f - g2);
    else if (g == v)
        *h = (b == m ? 1.0f + r2 : 3.0f - b2);
    else
        *h = (r == m ? 3.0f + g2 : 5.0f - r2);
    *h /= 6.0;
}

void hsl2rgb(float h, float sl, float l, float *r, float *g, float *b)
{
    float v;
    *r = l;
    *g = l;
    *b = l;
    v = (l <= 0.5f) ? (l * (1.0f + sl)) : (l + sl - l * sl);
    if (v > 0.0f) {
        float m;
        float sv;
        int sextant;
        float fract, vsf, mid1, mid2;
        m = l + l - v;
        sv = (v - m ) / v;
        h *= 6.0f;
        sextant = (int)h;
        fract = h - sextant;
        vsf = v * sv * fract;
        mid1 = m + vsf;
        mid2 = v - vsf;
        switch (sextant) {
            case 0:
                *r = v;
                *g = mid1;
                *b = m;
             break;
             case 1:
                 *r = mid2;
                 *g = v;
                 *b = m;
             break;
             case 2:
                 *r = m;
                 *g = v;
                 *b = mid1;
             break;
             case 3:
                 *r = m;
                 *g = mid2;
                 *b = v;
             break;
             case 4:
                 *r = mid1;
                 *g = m;
                 *b = v;
             break;
             case 5:
                 *r = v;
                 *g = m;
                 *b = mid2;
             break;
         }    
    } 
}

int findIndex(float *data, int size)
{
    float max = *std::max_element(data, data + size);
    int i;
    for (i = 0; i < size; i++)
        if (data[i] == max) 
            return i;

    return i;
}

void transformFromRgbToHsl(pfs::Array2D *R, pfs::Array2D *G, pfs::Array2D *B)
{
    int width = R->getCols();
    int height = R->getRows();
    float h, s, l;
    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*R)(i, j), (*G)(i, j), (*B)(i, j), &h, &s, &l);
            (*R)(i, j) = h;
            (*G)(i, j) = s;
            (*B)(i, j) = l;
        }
    } 
}

void transformFromHslToRgb(pfs::Array2D *R, pfs::Array2D *G, pfs::Array2D *B)
{
    int width = R->getCols();
    int height = R->getRows();
    float r, g, b;
    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            hsl2rgb((*R)(i, j), (*G)(i, j), (*B)(i, j), &r, &g, &b);
            (*R)(i, j) = r;
            (*G)(i, j) = g;
            (*B)(i, j) = b;
        }
    } 
}

float hueMean(float *hues, int size)
{
    float H = 0.0f;
    for (int k = 0; k < size; k++)
        H += hues[k];

    return H / size;
}

float hueSquaredMean(Array2DList &listH, int k)
{
    int width = listH.at(0)->getCols();
    int height = listH.at(0)->getRows();
    int size = listH.size();
    float hues[size];
    
    float Fk, Fh;
    float HS = 0.0f;
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            for (int h = 0; h < size; h++) {
                Fh = (*listH.at(h))(i, j);
                if (std::isnan(Fh)) Fh = 0.0f;
                hues[h] = Fh;
            }
            Fk = (*listH.at(k))(i, j);
            if (std::isnan(Fk)) Fk = 0.0f;
            float H = hueMean(hues, size) - Fk;
            H = H*H;
            HS += H;
        }
    }
    
    return HS / (width*height);
}

float computeK(pfs::Array2D *Fopt, pfs::Array2D *F, int idxOpt, int idx, int i, int j)
{
    float Ft = (*Fopt)(i, j) - (*F)(i, j);
    
    if (idxOpt < idx)
        Ft *= -1.0f;

    float Fx = ( (*Fopt)(i + 1, j) - (*Fopt)(i - 1, j) ) * 0.5f;
    float Fy = ( (*Fopt)(i, j + 1) - (*Fopt)(i, j - 1 ) ) * 0.5f;

    qDebug() << "Ft: " << Ft << " Fx: " <<  Fx << " Fy: " << Fy;
    return Ft + i * Fx + j * Fy;
}

void computeC(pfs::Array2D *F, int i, int j, gsl_vector *c)
{
    float Fx = ( (*F)(i + 1, j) - (*F)(i - 1, j) ) * 0.5f;
    float Fy = ( (*F)(i, j + 1) - (*F)(i, j - 1 ) ) * 0.5f;

    gsl_vector_set(c, 0, i * Fx);
    gsl_vector_set(c, 1, j * Fy);
    gsl_vector_set(c, 2, i * Fy);
    gsl_vector_set(c, 3, j * Fx);
    gsl_vector_set(c, 4, Fx);
    gsl_vector_set(c, 5, Fy);
}

void fillMatrixM1(gsl_matrix *M, gsl_vector *v)
{
    for (int i = 0; i < 6; i++) {
        gsl_matrix_set(M, i, 0, gsl_vector_get(v, i));
    }
}

void fillMatrixM2(gsl_matrix *M, gsl_vector *v)
{
    for (int i = 0; i < 6; i++) {
        gsl_matrix_set(M, 0, i, gsl_vector_get(v, i));
    }
}

void printMatrix(gsl_matrix *M, int rows, int cols)
{
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            printf ("m(%d,%d) = %g\n", i, j, gsl_matrix_get (M, i, j));
        }
    }
}

qreal averageLightness(pfs::Array2D *R, pfs::Array2D *G, pfs::Array2D *B)
{
    int width = R->getCols();
    int height = R->getRows();

    qreal avgLum = 0.0f;
    float h, s, l;
    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*R)(i, j), (*G)(i, j), (*B)(i, j), &h, &s, &l);
            avgLum += l;
        }
    } 
    return avgLum / (width * height);
}

qreal averageLightness(QImage *img)
{
    qreal avgLum = 0.0f;
    int w = img->width(), h = img->height();
    QColor color;
    QRgb rgb;
    qreal l;

    for (int j = 0; j < h; j++) {
        for (int i = 0; i < w; i++) {
            rgb = img->pixel(i, j);
            color = QColor::fromRgb(rgb);
            l = color.toHsl().lightnessF();
            avgLum += l;
        }
    }
    return avgLum / (w * h);
}

pfs::Array2D *shiftPfsArray2D(pfs::Array2D *in, int dx, int dy)
{
#ifdef TIMER_PROFILING
    msec_timer stop_watch;
    stop_watch.start();
#endif

    int width = in->getCols();
    int height = in->getRows();

    pfs::Array2D *temp = new pfs::Array2D(width, height);   
    pfs::Array2D *out = new pfs::Array2D(width, height);    
    
#pragma omp parallel for shared(temp)
    for (int j = 0; j < height; j++) 
        for (int i = 0; i < width; i++) 
            (*temp)(i, j) = 0;

    // x-shift
#pragma omp parallel for shared(in)
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            if ((i+dx) < 0)
                continue;
            if ((i+dx) >= width)
                break;
            if ((*in)(i+dx, j) > 65535)
                (*temp)(i, j) = 65535;
            else if ((*in)(i+dx, j) < 0)
                (*temp)(i, j) = 0;
            else
                (*temp)(i, j) = (*in)(i+dx, j);
        }
    }
    // y-shift
#pragma omp parallel for shared(out)
    for (int i = 0; i < width; i++) {
        for (int j = 0; j < height; j++) {
            if ((j+dy) < 0)
                continue;
            if ((j+dy) >= height)
                break;
            if ((*temp)(i, j+dy) > 65535)
                (*out)(i, j) = 65535;
            else if ((*temp)(i, j+dy) < 0)
                (*out)(i, j) = 0;
            else
                (*out)(i, j) = (*temp)(i, j+dy);
        }
    }
#ifdef TIMER_PROFILING
    stop_watch.stop_and_update();
    std::cout << "shiftPfsArray2D = " << stop_watch.get_time() << " msec" << std::endl;
#endif

    delete temp;
    return out;
}

float *findMax(pfs::Array2D *R)
{
    int width = R->getCols();
    int height = R->getRows();

    return std::max_element(R->getRawData(), R->getRawData() + width*height);
}

float *findMax(pfs::Array2D *R1, pfs::Array2D *G1, pfs::Array2D *B1)
{
    float *maxR1 = findMax(R1);
    float *maxG1 = findMax(G1);
    float *maxB1 = findMax(B1);

    float m1[] = {*maxR1, *maxG1, *maxB1};

    return std::max_element(m1, m1+3);
}

void blend(QImage *img1, QImage *img2, QImage *mask)
{
    qDebug() << "blend";
#ifdef TIMER_PROFILING
    msec_timer stop_watch;
    stop_watch.start();
#endif

    int width = img1->width();
    int height = img1->height();

    QColor color;
    QRgb maskValue, pixValue;
    qreal alpha;
    qreal avgLight1 = averageLightness(img1);
    qreal avgLight2 = averageLightness(img2);
    qreal sf = avgLight1 / avgLight2;
    int h, s, l;
    
    if (sf > 1.0f) sf = 1.0f / sf; 

    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            maskValue = mask->pixel(i,j);
            alpha = qAlpha(maskValue) / 255;
            pixValue = img2->pixel(i, j);
            color = QColor::fromRgb(pixValue).toHsl();
            color.getHsl(&h, &s, &l);
            l *= sf;
            color.setHsl(h, s, l);
            pixValue = color.rgb();     
            pixValue = (1.0f - alpha) * img1->pixel(i, j) +  alpha * pixValue;
            img1->setPixel(i, j, pixValue);
        }
    } 
#ifdef TIMER_PROFILING
    stop_watch.stop_and_update();
    std::cout << "blend = " << stop_watch.get_time() << " msec" << std::endl;
#endif
}

void blend(pfs::Array2D *R1, pfs::Array2D *G1, pfs::Array2D *B1, pfs::Array2D *R2, pfs::Array2D *G2, pfs::Array2D *B2, QImage *mask)
{
    qDebug() << "blend MDR";
#ifdef TIMER_PROFILING
    msec_timer stop_watch;
    stop_watch.start();
#endif

    int width = R1->getCols();
    int height = R1->getRows();

    QRgb maskValue;
    float alpha;
    qreal avgLight1 = averageLightness(R1, G1, B1);
    qreal avgLight2 = averageLightness(R2, G2, B2);
    qreal sf = avgLight1 / avgLight2;
    float h, s, l, r1, g1, b1, r2, g2, b2;

    float *max1 = findMax(R1, G1, B1);    
    float *max2 = findMax(R2, G2, B2);    
    float max = std::max(*max1, *max2);

    if (sf > 1.0f) sf = 1.0f / sf; 
    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            maskValue = mask->pixel(i,j);
            alpha = qAlpha(maskValue) / 255;
            r1 = (*R1)(i, j) / max;
            g1 = (*G1)(i, j) / max;
            b1 = (*B1)(i, j) / max;

            r2 = (*R2)(i, j) / max;
            g2 = (*G2)(i, j) / max;
            b2 = (*B2)(i, j) / max;

            rgb2hsl(r2, g2, b2, &h, &s, &l);
            l *= sf;
            hsl2rgb(h, s, l, &r2, &g2, &b2);
            (*R1)(i, j) = (1.0f - alpha) * r1 +  alpha * r2;
            (*G1)(i, j) = (1.0f - alpha) * g1 +  alpha * g2;
            (*B1)(i, j) = (1.0f - alpha) * b1 +  alpha * b2;
        }
    } 
#ifdef TIMER_PROFILING
    stop_watch.stop_and_update();
    std::cout << "blend MDR = " << stop_watch.get_time() << " msec" << std::endl;
#endif
}

void normalize(pfs::Array2D *R)
{
    int width = R->getCols();
    int height = R->getRows();

    float max = *findMax(R);

    std::transform(R->getRawData(), R->getRawData() + width*height, R->getRawData(), std::bind2nd(std::divides<float>(),max));
}

void normalize(pfs::Array2D *R, pfs::Array2D *G, pfs::Array2D *B)
{
    int width = R->getCols();
    int height = R->getRows();

    float max = *findMax(R, G, B);

    std::transform(R->getRawData(), R->getRawData() + width*height, R->getRawData(), std::bind2nd(std::divides<float>(),max));
    std::transform(G->getRawData(), G->getRawData() + width*height, G->getRawData(), std::bind2nd(std::divides<float>(),max));
    std::transform(B->getRawData(), B->getRawData() + width*height, B->getRawData(), std::bind2nd(std::divides<float>(),max));
}

void computeDifference(pfs::Array2D *R1, pfs::Array2D *G1, pfs::Array2D *B1, pfs::Array2D *R2, pfs::Array2D *G2, pfs::Array2D *B2, float threshold)
{
    int width = R1->getCols();
    int height = R1->getRows();
    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            float r = std::abs((*R1)(i, j) - (*R2)(i, j));
            float g = std::abs((*G1)(i, j) - (*G2)(i, j));
            float b = std::abs((*B1)(i, j) - (*B2)(i, j));
            (*R1)(i, j) = (r < threshold) ? 0.0f : r;
            (*G1)(i, j) = (g < threshold) ? 0.0f : g;
            (*B1)(i, j) = (b < threshold) ? 0.0f : b;
        }
    }
}

void computeLightnessDifference(pfs::Array2D *L1, pfs::Array2D *L2, pfs::Array2D *map, float threshold)
{
    int width = L1->getCols();
    int height = L1->getRows();
    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            float v = std::abs((*L1)(i, j) - (*L2)(i, j));
            (*map)(i, j) = (v < threshold) ? 0.0f : v;
        }
    }
}

void computeColorDifference(pfs::Array2D *R1, pfs::Array2D *G1, pfs::Array2D *B1, 
                             pfs::Array2D *R2, pfs::Array2D *G2, pfs::Array2D *B2,
                             pfs::Array2D *outR, pfs::Array2D *outG, pfs::Array2D *outB, 
                             float threshold)
{
    int width = R1->getCols();
    int height = R1->getRows();
    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            float dr = std::abs((*R1)(i, j) - (*R2)(i, j));
            float dg = std::abs((*G1)(i, j) - (*G2)(i, j));
            float db = std::abs((*B1)(i, j) - (*B2)(i, j));
            if ((dr < threshold) && (dg < threshold) && (db < threshold)) {
                (*outR)(i, j) = 0.0f;
                (*outG)(i, j) = 0.0f;
                (*outB)(i, j) = 0.0f;
            }
            else
            {
                (*outR)(i, j) = dr;
                (*outG)(i, j) = dg;
                (*outB)(i, j) = db;
            }
        }
    }
}

void partition(pfs::Array2D *image, QList<float> &set1, QList<float> &set2, float threshold)
{
    int size = image->getCols() * image->getRows();
    
    for (int i = 0; i < size; i++)
        if ((*image)(i) < threshold) 
            set1.append((*image)(i));
        else
            set2.append((*image)(i));
}

float computeMean(QList<float> &list)
{
    float mean = 0.0f;
    
    foreach(float v, list)
        mean += v*v;

    return mean / list.count();
}

void histogramSegmentation(pfs::Array2D *image, float eps)
{
    int size = image->getCols() * image->getRows();
    float T1 = 0.5f, T2;
    QList<float> set1, set2;

    do {
        T2 = T1;
        partition(image, set1, set2, T1);
        float avg1 = computeMean(set1);
        float avg2 = computeMean(set2);
        T1 = (avg1 + avg2) * 0.5f;
        if (std::isnan(T1))
            T1 = T2 * 0.5f;
        set1.clear();
        set2.clear();
        qDebug() << "delta = " << std::abs(T1 - T2);
    }
    while (std::abs(T1 - T2) > eps);  
    
    for (int i = 0; i < size; i++)
        if ((*image)(i) < T1)
            (*image)(i) = 0.0f; 
    
    qDebug() << "Done";
}    

void histogramSegmentation(pfs::Array2D *R, pfs::Array2D *G, pfs::Array2D *B, float eps)
{
    int size = R->getCols() * R->getRows();
    float T1 = 0.5f, T2;
    QList<float> setR1, setG1, setB1, setR2, setG2, setB2;

    do {
        T2 = T1;
        partition(R, setR1, setR2, T1);
        partition(G, setG1, setG2, T1);
        partition(B, setB1, setB2, T1);
        float avgR1 = computeMean(setR1);
        float avgG1 = computeMean(setG1);
        float avgB1 = computeMean(setB1);
        float avgR2 = computeMean(setR2);
        float avgG2 = computeMean(setG2);
        float avgB2 = computeMean(setB2);
        T1 = (avgR1 + avgG1 + avgB1 + avgR2 + avgG2 + avgB2) / 6.0f;
        if (std::isnan(T1))
            T1 = T2 * 0.5f;
        setR1.clear();
        setG1.clear();
        setB1.clear();
        setR2.clear();
        setG2.clear();
        setB2.clear();
        qDebug() << "delta = " << std::abs(T1 - T2);
    }
    while (std::abs(T1 - T2) > eps);  

    for (int i = 0; i < size; i++) {
        if ((*R)(i) < T1 || (*G)(i) < T1 || (*B)(i) < T1) {
                (*R)(i) = 0.0f;
                (*G)(i) = 0.0f;
                (*B)(i) = 0.0f;
        }
    }
}

void createMask(pfs::Array2D *R, pfs::Array2D *G, pfs::Array2D *B, QImage *mask, float eps)
{
    uchar *data = mask->bits();    

    int width = R->getCols();
    int height = R->getRows();

    pfs::Array2D *tempR, *tempG, *tempB;
    tempR = new pfs::Array2D(width, height);
    tempG = new pfs::Array2D(width, height);
    tempB = new pfs::Array2D(width, height);
    
    pfs::copyArray(R, tempR);
    pfs::copyArray(B, tempG);
    pfs::copyArray(G, tempB);
    
    normalize(tempR, tempG, tempB);

    float h, s, l;
    // convert to hsl and scale lightness (R, G and B will contain the H, S and L values)
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*tempR)(i, j), (*tempG)(i, j), (*tempB)(i, j), &h, &s, &l); 
            (*tempR)(i, j) = h;      
            (*tempG)(i, j) = s;      
            (*tempB)(i, j) = l;      
        }
    }    
    histogramSegmentation(tempB, eps);   

    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            if ((*tempB)(i, j) == 0.0f) {
                *(data + 4*(i + j*width) + 0) = 0; // alpha
                *(data + 4*(i + j*width) + 1) = 0; // red
                *(data + 4*(i + j*width) + 2) = 0; // green
                *(data + 4*(i + j*width) + 3) = 0; // blue
            }
            else {
                *(data + 4*(i + j*width) + 0) = 255; // alpha
                *(data + 4*(i + j*width) + 1) = 0;   // red
                *(data + 4*(i + j*width) + 2) = 0;   // green
                *(data + 4*(i + j*width) + 3) = 255; // blue
            }
        }
    }
    delete tempR;
    delete tempG;
    delete tempB;
} 


void createMask(pfs::Array2D *R1, pfs::Array2D *G1, pfs::Array2D *B1, pfs::Array2D *R2, pfs::Array2D *G2, pfs::Array2D *B2, 
    QImage *mask, float threshold)
{
    uchar *data = mask->bits();    

    int width = R1->getCols();
    int height = R1->getRows();

    pfs::Array2D *tempR1, *tempG1, *tempB1, *tempR2, *tempG2, *tempB2;
    tempR1 = new pfs::Array2D(width, height);
    tempG1 = new pfs::Array2D(width, height);
    tempB1 = new pfs::Array2D(width, height);
    tempR2 = new pfs::Array2D(width, height);
    tempG2 = new pfs::Array2D(width, height);
    tempB2 = new pfs::Array2D(width, height);

    pfs::copyArray(R1, tempR1);
    pfs::copyArray(B1, tempG1);
    pfs::copyArray(G1, tempB1);
    pfs::copyArray(R2, tempR2);
    pfs::copyArray(G2, tempG2);
    pfs::copyArray(B2, tempB2);

    qreal avgLight1 = averageLightness(tempR1, tempG1, tempB1);
    qreal avgLight2 = averageLightness(tempR2, tempG2, tempB2);
    qreal sf = avgLight1 / avgLight2;

    if (sf > 1.0f) sf = 1.0f / sf; 

    normalize(tempR1, tempG1, tempB1);
    normalize(tempR2, tempG2, tempB2);

    float h, s, l;
    // convert to hsl and scale lightness (R, G and B will contain the H, S and L values)
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*tempR1)(i, j), (*tempG1)(i, j), (*tempB1)(i, j), &h, &s, &l); 
            (*tempR1)(i, j) = h;      
            (*tempG1)(i, j) = s;      
            (*tempB1)(i, j) = l;      
        }
    }    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*tempR2)(i, j), (*tempG2)(i, j), (*tempB2)(i, j), &h, &s, &l); 
            (*tempR2)(i, j) = h;      
            (*tempG2)(i, j) = s;      
            (*tempB2)(i, j) = sf * l;      
        }
    }    

    float max;
    float *maxB1 = std::max_element(tempB1->getRawData(), tempB1->getRawData() + width*height);
    float *maxB2 = std::max_element(tempB2->getRawData(), tempB2->getRawData() + width*height);

    max = std::max(*maxB1, *maxB2);

    std::transform(tempB1->getRawData(), tempB1->getRawData() + width*height, tempB1->getRawData(), std::bind2nd(std::divides<float>(),max));
    std::transform(tempB2->getRawData(), tempB2->getRawData() + width*height, tempB2->getRawData(), std::bind2nd(std::divides<float>(),max));
        
    pfs::Array2D *lightnessMap = new pfs::Array2D(width, height);
    
    computeLightnessDifference(tempB1, tempB2, lightnessMap, threshold);

    float r, g, b;
    // back to rgb again
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            hsl2rgb((*tempR1)(i, j), (*tempG1)(i, j), (*tempB1)(i, j), &r, &g, &b);
            (*tempR1)(i, j) = r;      
            (*tempG1)(i, j) = g;      
            (*tempB1)(i, j) = b;      
        }
    }
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            hsl2rgb((*tempR2)(i, j), (*tempG2)(i, j), (*tempB2)(i, j), &r, &g, &b);
            (*tempR2)(i, j) = r;      
            (*tempG2)(i, j) = g;      
            (*tempB2)(i, j) = b;      
        }
    }

    // this will override 1st image data
    computeDifference(tempR1, tempB1, tempG1, tempR2, tempG2, tempB2, 0.01);
    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            if ((*lightnessMap)(i,j) < threshold) {
                *(data + 4*(i + j*width) + 0) = 0; // alpha
                *(data + 4*(i + j*width) + 1) = 0; // red
                *(data + 4*(i + j*width) + 2) = 0; // green
                *(data + 4*(i + j*width) + 3) = 0; // blue
            }
            else {
                *(data + 4*(i + j*width) + 0) = 255; // alpha
                *(data + 4*(i + j*width) + 1) = 0;   // red
                *(data + 4*(i + j*width) + 2) = 0;   // green
                *(data + 4*(i + j*width) + 3) = 255; // blue
            }
        }
    }
    
    mask->save("nuovamaschera1.jpg");

    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            if ((*tempR1)(i, j) < threshold || (*tempG1)(i, j) < threshold || (*tempB1)(i, j) < threshold) {
                *(data + 4*(i + j*width) + 0) = 0; // alpha
                *(data + 4*(i + j*width) + 1) = 0; // red
                *(data + 4*(i + j*width) + 2) = 0; // green
                *(data + 4*(i + j*width) + 3) = 0; // blue
            }
            else {
                *(data + 4*(i + j*width) + 0) = 255; // alpha
                *(data + 4*(i + j*width) + 1) = 0;   // red
                *(data + 4*(i + j*width) + 2) = 0;   // green
                *(data + 4*(i + j*width) + 3) = 255; // blue
            }
        }
    }
        
    mask->save("nuovamaschera2.jpg");

    delete tempR1;
    delete tempG1;
    delete tempB1;
    delete tempR2;
    delete tempG2;
    delete tempB2;

    qDebug() << "Done";
}
}
//
// ----------------------------------------------------------------------------------
//
HdrCreationManager::HdrCreationManager(bool fromCommandLine) :
    inputType( UNKNOWN_INPUT_TYPE ),
    chosen_config( predef_confs[0] ),
    ais( NULL ),
    m_shift(0),
    fromCommandLine( fromCommandLine )
{}

void HdrCreationManager::setConfig(const config_triple &c)
{
    chosen_config = c;
}

void HdrCreationManager::setFileList(const QStringList& l)
{
    processedFiles = m_shift;
    runningThreads = 0;
    loadingError = false;

    fileList.append(l);

    expotimes.resize(fileList.count());
    filesToRemove.resize(fileList.count());

    // add default values
    for (int i = 0; i < l.count(); i++)
    {
        // time equivalents of EV values
        expotimes[m_shift + i] = -1;
        // i-th==true means we started a thread to load the i-th file
        startedProcessing.append(false);

        mdrImagesList.push_back(NULL);
        antiGhostingMasksList.push_back(NULL); 
        // ldr payloads
        ldrImagesList.push_back(NULL);
        // mdr payloads
        listmdrR.push_back(NULL);
        listmdrG.push_back(NULL);
        listmdrB.push_back(NULL);
    }
}

void HdrCreationManager::loadInputFiles()
{
    //find first not started processing.
    int firstNotStarted = -1;
    for (int i = 0; i < fileList.size(); i++)
    {
        if ( !startedProcessing.at(i) )
        {
            firstNotStarted = i;
            //qDebug("HCM: loadInputFiles: found not startedProcessing: %d",i);
            break;
        }
    }

    // we can end up in this function "conditionalLoadInput" many times,
    // called in a queued way by newResult(...).
    if (firstNotStarted == -1)
    {
        if (processedFiles == fileList.size()) //then it's really over
        {
            if (filesLackingExif.size() == 0)
            {
                //give an offset to the EV values if they are outside of the -10..10 range.
                checkEVvalues();
            }
            emit finishedLoadingInputFiles(filesLackingExif);
        } //all files loaded
        
        //return when list is over but some threads are still running.
        return;
    } //if all files already started processing
    else
    { //if we still have to start processing some file
        while ( runningThreads < m_luminance_options.getNumThreads() &&
                firstNotStarted < startedProcessing.size() )
        {
            startedProcessing[firstNotStarted] = true;
            HdrInputLoader *thread = new HdrInputLoader(fileList[firstNotStarted],firstNotStarted);
            if (thread == NULL)
                exit(1); // TODO: show an error message and exit gracefully
            connect(thread, SIGNAL(finished()), thread, SLOT(deleteLater()));
            connect(thread, SIGNAL(loadFailed(QString,int)), this, SLOT(loadFailed(QString,int)));
            connect(thread, SIGNAL(ldrReady(QImage *, int, float, QString, bool)), this, SLOT(ldrReady(QImage *, int, float, QString, bool)));
            connect(thread, SIGNAL(mdrReady(pfs::Frame *, int, float, QString)), this, SLOT(mdrReady(pfs::Frame *, int, float, QString)));
            connect(thread, SIGNAL(maximumValue(int)), this, SIGNAL(maximumValue(int)));
            connect(thread, SIGNAL(nextstep(int)), this, SIGNAL(nextstep(int)));
            thread->start();
            firstNotStarted++;
            runningThreads++;
        }
    }
}

void HdrCreationManager::loadFailed(const QString& message, int /*index*/)
{
    //check for correct image size: update list that will be sent once all is over.
    loadingError = true;
    emit errorWhileLoading(message);
}

void HdrCreationManager::mdrReady(pfs::Frame* newFrame, int index, float expotime, const QString& newfname)
{
    if (loadingError) {
        emit processed();
        return;
    }
    //newFrame is in CS_RGB but channel names remained X Y Z
    pfs::Channel *R, *G, *B;
    newFrame->getXYZChannels(R, G, B);

    if (inputType == LDR_INPUT_TYPE)
    {
        loadingError = true;
        emit errorWhileLoading(tr("The image %1 is an 8 bit format (LDR) while the previous ones are not.").arg(newfname));
        return;
    }
    inputType = MDR_INPUT_TYPE;
    if (!mdrsHaveSameSize(R->getWidth(),R->getHeight()))
    {
        loadingError = true;
        emit errorWhileLoading(tr("The image %1 has an invalid size.").arg(newfname));
        return;
    }
    if (!fromCommandLine) {
        mdrImagesList[index] = fromHDRPFStoQImage(newFrame);
        QImage *img = new QImage(R->getWidth(),R->getHeight(), QImage::Format_ARGB32);
        img->fill(qRgba(0,0,0,0));
        antiGhostingMasksList[index] = img;
    }
    m_mdrWidth = R->getWidth();
    m_mdrHeight = R->getHeight();
    // fill with image data
    listmdrR[index] = R->getChannelData();
    listmdrG[index] = G->getChannelData();
    listmdrB[index] = B->getChannelData();
    //perform some housekeeping
    newResult(index,expotime,newfname);
    //continue with the loading process
    loadInputFiles();
}

void HdrCreationManager::ldrReady(QImage* newImage, int index, float expotime, const QString& newfname, bool /*ldrtiff*/)
{
    //qDebug("HCM: ldrReady");
    if (loadingError)
    {
        emit processed();
        return;
    }
    if (inputType==MDR_INPUT_TYPE)
    {
        loadingError = true;
        emit errorWhileLoading(tr("The image %1 is an 16 bit format while the previous ones are not.").arg(newfname));
        return;
    }
    inputType=LDR_INPUT_TYPE;
    if (!ldrsHaveSameSize(newImage->width(),newImage->height()))
    {
        loadingError = true;
        emit errorWhileLoading(tr("The image %1 has an invalid size.").arg(newfname));
        return;
    }

    // fill with image data
    ldrImagesList[index] = newImage;
    if (!fromCommandLine) {
        QImage *img = new QImage(newImage->width(),newImage->height(), QImage::Format_ARGB32);
        img->fill(qRgba(0,0,0,0));
        antiGhostingMasksList[index] = img;
    }

    //perform some housekeeping
    newResult(index,expotime,newfname);
    //continue with the loading process
    loadInputFiles();
}

void HdrCreationManager::newResult(int index, float expotime, const QString& newfname)
{
    runningThreads--;
    processedFiles++;

    //update filesToRemove
    if ( fileList.at(index) != newfname )
    {
        qDebug() << "Files to remove " << index << " " << newfname;
        filesToRemove[index] = newfname;
    }

    //update expotimes[i]
    expotimes[index] = expotime;

    QFileInfo qfi(fileList[index]);
    //check for invalid exif: update list that will be sent once all is over.
    if (expotimes[index] == -1)
    {
        filesLackingExif << "<li>"+qfi.fileName()+"</li>";
    }

    emit fileLoaded(index,fileList[index],expotimes[index]);
    emit processed();
}

bool HdrCreationManager::ldrsHaveSameSize(int currentWidth, int currentHeight)
{
    for (int i = 0; i < ldrImagesList.size(); i++)
    {
        const QImage* imagepointer = ldrImagesList.at(i);
        if (imagepointer != NULL)
        {
            if ( (imagepointer->width() != currentWidth) ||
                 (imagepointer->height() != currentHeight) )
            {
                return false;
            }
        }
    }
    return true;
}

bool HdrCreationManager::mdrsHaveSameSize(int currentWidth, int currentHeight)
{
    for (unsigned int i = 0; i < listmdrR.size(); i++)
    {
        const pfs::Array2D* Rpointer = listmdrR.at(i);
        const pfs::Array2D* Gpointer = listmdrG.at(i);
        const pfs::Array2D* Bpointer = listmdrB.at(i);
        if (Rpointer != NULL && Gpointer != NULL && Bpointer != NULL)
        {
            if ( (Rpointer->getCols() != currentWidth) ||
                 (Rpointer->getRows() != currentHeight) ||
                 (Gpointer->getCols() != currentWidth) ||
                 (Gpointer->getRows() != currentHeight) ||
                 (Bpointer->getCols() != currentWidth) ||
                 (Bpointer->getRows() != currentHeight) )
            {
                return false;
            }
        }
    }
    return true;
}

void HdrCreationManager::align_with_mtb()
{
    mtb_alignment(ldrImagesList);
    emit finishedAligning(0);
}

void HdrCreationManager::set_ais_crop_flag(bool flag)
{
    ais_crop_flag = flag;
}

void HdrCreationManager::align_with_ais()
{
    ais = new QProcess(this);
    if (ais == NULL) //TODO: exit gracefully
        exit(1);
    if (!fromCommandLine)
        ais->setWorkingDirectory(m_luminance_options.getTempDir());
    QStringList env = QProcess::systemEnvironment();
    #ifdef WIN32
    QString separator(";");
    #else
    QString separator(":");
    #endif
    env.replaceInStrings(QRegExp("^PATH=(.*)", Qt::CaseInsensitive), "PATH=\\1"+separator+QCoreApplication::applicationDirPath());
    ais->setEnvironment(env);
    connect(ais, SIGNAL(finished(int,QProcess::ExitStatus)), this, SLOT(ais_finished(int,QProcess::ExitStatus)));
    connect(ais, SIGNAL(error(QProcess::ProcessError)), this, SIGNAL(ais_failed(QProcess::ProcessError)));
    connect(ais, SIGNAL(error(QProcess::ProcessError)), this, SLOT(ais_failed_slot(QProcess::ProcessError)));
    connect(ais, SIGNAL(readyRead()), this, SLOT(readData()));
    
    QStringList ais_parameters = m_luminance_options.getAlignImageStackOptions();
    if (ais_crop_flag){
        ais_parameters << "-C";
    }
    if (filesToRemove[0] == "") {
        ais_parameters << fileList;
    }
    else {
        foreach(QString fname, filesToRemove) 
            ais_parameters << fname;    
    }
    qDebug() << "ais_parameters " << ais_parameters;
    #ifdef Q_WS_MAC
    ais->start(QCoreApplication::applicationDirPath()+"/align_image_stack", ais_parameters );
    #else
    ais->start("align_image_stack", ais_parameters );
    #endif
    qDebug() << "ais started";
}

void HdrCreationManager::ais_finished(int exitcode, QProcess::ExitStatus exitstatus)
{
    if (exitstatus != QProcess::NormalExit)
    {
        qDebug() << "ais failed";
        //emit ais_failed(QProcess::Crashed);
        return;
    }
    if (exitcode == 0)
    {
        //TODO: try-catch 
        clearlists(false);
        for (int i = 0; i < fileList.size(); i++)
        {
            //align_image_stack can only output tiff files
            QString filename;
            if (!fromCommandLine)
                filename = QString(m_luminance_options.getTempDir() + "/aligned_" + QString("%1").arg(i,4,10,QChar('0'))+".tif");
            else
                filename = QString("aligned_" + QString("%1").arg(i,4,10,QChar('0'))+".tif");
            QByteArray fname = QFile::encodeName(filename);
            TiffReader reader(fname, "", false);
            //if 8bit ldr tiff
            if (reader.is8bitTiff())
            {
                QImage* resultImage = reader.readIntoQImage();
                HdrInputLoader::conditionallyRotateImage(QFileInfo(fileList[0]), &resultImage);

                ldrImagesList.append( resultImage );
                if (!fromCommandLine) {
                    QImage *img = new QImage(resultImage->width(),resultImage->height(), QImage::Format_ARGB32);
                    img->fill(qRgba(0,0,0,0));
                    antiGhostingMasksList.append(img);
                }
            }
            //if 16bit (tiff) treat as hdr
            else if (reader.is16bitTiff())
            {
                //TODO: get a 16bit TIFF image and test it
                pfs::Frame *newFrame = reader.readIntoPfsFrame();
                m_mdrWidth = newFrame->getWidth();
                m_mdrHeight = newFrame->getHeight();
                pfs::Channel *R, *G, *B;
                R = newFrame->getChannel("X");
                G = newFrame->getChannel("Y");
                B = newFrame->getChannel("Z");
                listmdrR.push_back(R->getChannelData());
                listmdrG.push_back(G->getChannelData());
                listmdrB.push_back(B->getChannelData());
                if (!fromCommandLine) {
                    mdrImagesList.append(fromHDRPFStoQImage(newFrame));
                    QImage *img = new QImage(R->getWidth(),R->getHeight(), QImage::Format_ARGB32);
                    img->fill(qRgba(0,0,0,0));
                    antiGhostingMasksList.append(img);
                }
            }
            qDebug() << "void HdrCreationManager::ais_finished: remove " << fname;
            QFile::remove(fname);
        }
        QFile::remove(m_luminance_options.getTempDir() + "/hugin_debug_optim_results.txt");
        emit finishedAligning(exitcode);
    }
    else
    {
        qDebug() << "align_image_stack exited with exit code " << exitcode;
        emit finishedAligning(exitcode);
    }
}

void HdrCreationManager::ais_failed_slot(QProcess::ProcessError error)
{
    qDebug() << "align_image_stack failed";
}

void HdrCreationManager::removeTempFiles()
{
    foreach (QString tempfname, filesToRemove)
    {
        qDebug() << "void HdrCreationManager::removeTempFiles(): " << qPrintable(tempfname);
        if (!tempfname.isEmpty())
        {
            QFile::remove(tempfname);
        }
    }
    filesToRemove.clear();
}

void HdrCreationManager::checkEVvalues()
{
    float max=-20, min=+20;
    for (int i = 0; i < fileList.size(); i++) {
        float ev_val = log2f(expotimes[i]);
        if (ev_val > max)
            max = ev_val;
        if (ev_val < min)
            min = ev_val;
    }
    //now if values are out of bounds, add an offset to them.
    if (max > 10) {
        for (int i = 0; i < fileList.size(); i++) {
            float new_ev = log2f(expotimes[i]) - (max - 10);
            expotimes[i] = exp2f(new_ev);
            emit expotimeValueChanged(exp2f(new_ev), i);
        }
    } else if (min < -10) {
        for (int i = 0; i < fileList.size(); i++) {
            float new_ev = log2f(expotimes[i]) - (min + 10);
            expotimes[i] = exp2f(new_ev);
            emit expotimeValueChanged(exp2f(new_ev), i);
        }
    }
    //qDebug("HCM::END checkEVvalues");
}

void HdrCreationManager::setEV(float new_ev, int image_idx)
{
    if (expotimes[image_idx] == -1) {
        //remove always the first one
        //after the initial printing we only need to know the size of the list
        filesLackingExif.removeAt(0);
    }
    expotimes[image_idx] = exp2f(new_ev);
    emit expotimeValueChanged(exp2f(new_ev), image_idx);
}

pfs::Frame* HdrCreationManager::createHdr(bool ag, int iterations)
{
    //CREATE THE HDR
    if (inputType == LDR_INPUT_TYPE)
        return createHDR(expotimes.data(), &chosen_config, ag, iterations, true, &ldrImagesList );
    else
        return createHDR(expotimes.data(), &chosen_config, ag, iterations, false, &listmdrR, &listmdrG, &listmdrB );
}

HdrCreationManager::~HdrCreationManager()
{
    if (ais != NULL && ais->state() != QProcess::NotRunning) {
        ais->kill();
    }
    clearlists(true);
    qDeleteAll(antiGhostingMasksList);
}

void HdrCreationManager::clearlists(bool deleteExpotimeAsWell)
{
    startedProcessing.clear();
    filesLackingExif.clear();

    if (deleteExpotimeAsWell)
    {
        fileList.clear();
        expotimes.clear();
    }
    if (ldrImagesList.size() != 0)
    {
        qDeleteAll(ldrImagesList);
        ldrImagesList.clear();
        qDeleteAll(antiGhostingMasksList);
        antiGhostingMasksList.clear();
    }
    if (listmdrR.size()!=0 && listmdrG.size()!=0 && listmdrB.size()!=0)
    {
        Array2DList::iterator itR=listmdrR.begin(), itG=listmdrG.begin(), itB=listmdrB.begin();
        for (; itR!=listmdrR.end(); itR++,itG++,itB++ )
        {
            delete *itR;
            delete *itG;
            delete *itB;
        }
        listmdrR.clear();
        listmdrG.clear();
        listmdrB.clear();
        qDeleteAll(mdrImagesList);
        mdrImagesList.clear();
        qDeleteAll(mdrImagesToRemove);
        mdrImagesToRemove.clear();
        qDeleteAll(antiGhostingMasksList);
        antiGhostingMasksList.clear();
    }
}

void HdrCreationManager::makeSureLDRsHaveAlpha()
{
    if (ldrImagesList.at(0)->format()==QImage::Format_RGB32) {
        int origlistsize = ldrImagesList.size();
        for (int image_idx = 0; image_idx < origlistsize; image_idx++) {
            QImage *newimage = new QImage(ldrImagesList.at(0)->convertToFormat(QImage::Format_ARGB32));
            if (newimage == NULL)
                exit(1); // TODO: exit gracefully;
            ldrImagesList.append(newimage);
            delete ldrImagesList.takeAt(0);
        }
    }
}

void HdrCreationManager::applyShiftsToImageStack(const QList< QPair<int,int> > HV_offsets)
{
    int originalsize = ldrImagesList.count();
    //shift the images
    for (int i = 0; i < originalsize; i++) {
        if (HV_offsets[i].first == HV_offsets[i].second && HV_offsets[i].first == 0)
            continue;
        QImage *shifted = shiftQImage(ldrImagesList[i], HV_offsets[i].first, HV_offsets[i].second);
        delete ldrImagesList.takeAt(i);
        ldrImagesList.insert(i, shifted);
    }
}

void HdrCreationManager::applyShiftsToMdrImageStack(const QList< QPair<int,int> > HV_offsets)
{
    qDebug() << "HdrCreationManager::applyShiftsToMdrImageStack";
    int originalsize = mdrImagesList.count();
    for (int i = 0; i < originalsize; i++) {
        if (HV_offsets[i].first == HV_offsets[i].second && HV_offsets[i].first == 0)
            continue;
        pfs::Array2D *shiftedR = shiftPfsArray2D(listmdrR[i], HV_offsets[i].first, HV_offsets[i].second);
        pfs::Array2D *shiftedG = shiftPfsArray2D(listmdrG[i], HV_offsets[i].first, HV_offsets[i].second);
        pfs::Array2D *shiftedB = shiftPfsArray2D(listmdrB[i], HV_offsets[i].first, HV_offsets[i].second);
        delete listmdrR[i];
        delete listmdrG[i];
        delete listmdrB[i];
        listmdrR[i] = shiftedR;
        listmdrG[i] = shiftedG;
        listmdrB[i] = shiftedB;
    }
}


void HdrCreationManager::cropLDR(const QRect ca)
{
    //crop all the images
    int origlistsize = ldrImagesList.size();
    for (int image_idx = 0; image_idx < origlistsize; image_idx++) {
        QImage *newimage = new QImage(ldrImagesList.at(0)->copy(ca));
        if (newimage == NULL)
            exit(1); // TODO: exit gracefully
        ldrImagesList.append(newimage);
        delete ldrImagesList.takeAt(0);
    }
    cropAgMasks(ca);
}

void HdrCreationManager::cropMDR(const QRect ca)
{
    //crop all the images
    int origlistsize = listmdrR.size();
    pfs::Frame *frame;
    pfs::Channel *Xc, *Yc, *Zc;
    pfs::Frame *cropped_frame;
    for (int idx = 0; idx < origlistsize; idx++)
    {
        frame = pfs::DOMIO::createFrame( m_mdrWidth, m_mdrHeight );
        frame->createXYZChannels( Xc, Yc, Zc );
        Xc->setChannelData(listmdrR[idx]);  
        Yc->setChannelData(listmdrG[idx]);  
        Zc->setChannelData(listmdrB[idx]);  
        int x_ul, y_ul, x_br, y_br;
        ca.getCoords(&x_ul, &y_ul, &x_br, &y_br);
        cropped_frame = pfs::pfscut(frame, x_ul, y_ul, x_br, y_br);

        pfs::DOMIO::freeFrame(frame);

        pfs::Channel *R, *G, *B;
        cropped_frame->getXYZChannels( R, G, B);
        listmdrR[idx] = R->getChannelData();
        listmdrG[idx] = G->getChannelData();
        listmdrB[idx] = B->getChannelData();
        QImage *newimage = new QImage(mdrImagesList.at(0)->copy(ca));
        if (newimage == NULL)
            exit(1); // TODO: exit gracefully
        mdrImagesList.append(newimage);
        mdrImagesToRemove.append(mdrImagesList.takeAt(0));
        QImage *img = new QImage(R->getWidth(),R->getHeight(), QImage::Format_ARGB32);
        img->fill(qRgba(0,0,0,0));
        antiGhostingMasksList.append(img);
        antiGhostingMasksList.takeAt(0);
    }
    m_mdrWidth = cropped_frame->getWidth();
    m_mdrHeight = cropped_frame->getHeight();
    cropAgMasks(ca);
}

void HdrCreationManager::reset()
{
    ais = NULL;
    m_shift = 0;
    chosen_config = predef_confs[0];
    inputType = UNKNOWN_INPUT_TYPE;
    fileList.clear();
    clearlists(true);
    removeTempFiles();
}

void HdrCreationManager::remove(int index)
{
    switch (inputType) {
    case LDR_INPUT_TYPE:
    {
        ldrImagesList.removeAt(index);          
    }
        break;
    case MDR_INPUT_TYPE:
    {
            Array2DList::iterator itR = listmdrR.begin() + index;
            delete *itR;
            listmdrR.erase(itR);

            Array2DList::iterator itG = listmdrG.begin() + index;
            delete *itG;
            listmdrG.erase(itG);

            Array2DList::iterator itB = listmdrB.begin() + index;
            delete *itB;
            listmdrB.erase(itB);
            
            delete mdrImagesList[index];            
            mdrImagesList.removeAt(index);          
            
            QString fname = filesToRemove.at(index);
            qDebug() << "void HdrCreationManager::remove(int index): filename " << fname;
            QFile::remove(fname);
    }
        break;
        // ...in this case, do nothing!
    case UNKNOWN_INPUT_TYPE:
    default:{}
        break;
    }
    fileList.removeAt(index);
    filesToRemove.remove(index);
    expotimes.remove(index);
    startedProcessing.removeAt(index);
}

void HdrCreationManager::readData()
{
    QByteArray data = ais->readAll();
    emit aisDataReady(data);
}

void HdrCreationManager::saveLDRs(const QString filename)
{
#ifdef QT_DEBUG
    qDebug() << "HdrCreationManager::saveLDRs";
#endif

    int origlistsize = ldrImagesList.size();
    for (int idx = 0; idx < origlistsize; idx++)
    {
        QString fname = filename + QString("_%1").arg(idx) + ".tiff";
        TiffWriter writer(QFile::encodeName(fname).constData(), ldrImagesList[idx]);
        writer.write8bitTiff();

        QFileInfo qfi(filename);
        QString absoluteFileName = qfi.absoluteFilePath();
        QByteArray encodedName = QFile::encodeName(absoluteFileName + QString("_%1").arg(idx) + ".tiff");
        ExifOperations::copyExifData(QFile::encodeName(fileList[idx]).constData(), encodedName.constData(), false);
    }
    emit imagesSaved();
}

void HdrCreationManager::saveMDRs(const QString filename)
{
#ifdef QT_DEBUG
    qDebug() << "HdrCreationManager::saveMDRs";
#endif

    int origlistsize = listmdrR.size();
    for (int idx = 0; idx < origlistsize; idx++)
    {
        QString fname = filename + QString("_%1").arg(idx) + ".tiff";
        pfs::Frame *frame = pfs::DOMIO::createFrame( m_mdrWidth, m_mdrHeight );
        pfs::Channel *Xc, *Yc, *Zc;
        frame->createXYZChannels( Xc, Yc, Zc );
        Xc->setChannelData(listmdrR[idx]);  
        Yc->setChannelData(listmdrG[idx]);  
        Zc->setChannelData(listmdrB[idx]);  
        TiffWriter writer(QFile::encodeName(fname).constData(), frame);
        writer.writePFSFrame16bitTiff();

        QFileInfo qfi(filename);
        QString absoluteFileName = qfi.absoluteFilePath();
        QByteArray encodedName = QFile::encodeName(absoluteFileName + QString("_%1").arg(idx) + ".tiff");
        ExifOperations::copyExifData(QFile::encodeName(fileList[idx]).constData(), encodedName.constData(), false);
    }
    emit imagesSaved();
}

void HdrCreationManager::doAntiGhosting(int goodImageIndex)
{
    qDebug() << "HdrCreationManager::doAntiGhosting";
    if (inputType == LDR_INPUT_TYPE) {
        int origlistsize = ldrImagesList.size();
        for (int idx = 0; idx < origlistsize; idx++) {
            if (idx == goodImageIndex) continue;
            blend(ldrImagesList[idx], ldrImagesList[goodImageIndex], antiGhostingMasksList[idx]);
        }
    }
    else {
        int origlistsize = listmdrR.size();
        for (int idx = 0; idx < origlistsize; idx++) {
            if (idx == goodImageIndex) continue;
            blend(listmdrR[idx], listmdrG[idx], listmdrB[idx], 
                listmdrR[goodImageIndex], listmdrG[goodImageIndex], listmdrB[goodImageIndex],
                antiGhostingMasksList[idx]);
        }
    }       
}

void HdrCreationManager::cropAgMasks(QRect ca) {
    int origlistsize = antiGhostingMasksList.size();
    for (int image_idx = 0; image_idx < origlistsize; image_idx++) {
        QImage *newimage = new QImage(antiGhostingMasksList.at(0)->copy(ca));
        if (newimage == NULL)
            exit(1); // TODO: exit gracefully
        antiGhostingMasksList.append(newimage);
        delete antiGhostingMasksList.takeAt(0);
    }
}


QImage *HdrCreationManager::calculateAgMask(int index1, int index2, float threshold)
{
    int width = listmdrR[0]->getCols();
    int height = listmdrR[0]->getRows();
    QImage *newMask = new QImage(width, height, QImage::Format_ARGB32);
    createMask(listmdrR[index1], listmdrG[index1], listmdrB[index1],
                        listmdrR[index2], listmdrG[index2], listmdrB[index2],
                            newMask, threshold);
    return newMask;
}

QImage *HdrCreationManager::calculateAgMaskAlgo1(QRect rect, int index1, int index2, float threshold)
{
    int width = rect.width();
    int height = rect.height();
    pfs::Array2D *R1, *G1, *B1, *R2, *G2, *B2;
    
    R1 = new pfs::Array2D(width, height);
    G1 = new pfs::Array2D(width, height);
    B1 = new pfs::Array2D(width, height);
    R2 = new pfs::Array2D(width, height);
    G2 = new pfs::Array2D(width, height);
    B2 = new pfs::Array2D(width, height);

    int x_ul, y_ul, x_br, y_br;

    rect.getCoords(&x_ul, &y_ul, &x_br, &y_br);

    pfs::copyArray(listmdrR[index1], R1, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrG[index1], G1, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrB[index1], B1, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrR[index2], R2, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrG[index2], G2, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrB[index2], B2, x_ul, y_ul, x_br, y_br);

    QImage *newMask = new QImage(width, height, QImage::Format_ARGB32);
    uchar *data = newMask->bits();


    qreal avgLight1 = averageLightness(R1, G1, B1);
    qreal avgLight2 = averageLightness(R2, G2, B2);
    qreal sf = avgLight1 / avgLight2;

    if (sf > 1.0f) sf = 1.0f / sf; 


    normalize(R1, G1, B1);
    normalize(R2, G2, B2);   
    
    float h, s, l;
    // convert to hsl (R, G and B will contain the H, S and L values)
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*R1)(i, j), (*G1)(i, j), (*B1)(i, j), &h, &s, &l); 
            (*R1)(i, j) = h;      
            (*G1)(i, j) = s;      
            (*B1)(i, j) = l;      
        }
    }    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*R2)(i, j), (*G2)(i, j), (*B2)(i, j), &h, &s, &l); 
            (*R2)(i, j) = h;      
            (*G2)(i, j) = s;      
            (*B2)(i, j) = sf * l;      
        }
    }    
      
    pfs::Array2D *lightnessMap = new pfs::Array2D(width, height);
    
    computeLightnessDifference(B1, B2, lightnessMap, threshold);

    histogramSegmentation(lightnessMap, 1e-5);   
    QImage testImage(width, height, QImage::Format_ARGB32);
    uchar *testData = testImage.bits();
    
    // Fill the test mask
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            float v = (*lightnessMap)(i, j);
            *(testData + 4*(i + j*width) + 0) = 255; // alpha
            *(testData + 4*(i + j*width) + 1) = 255 * v; // red
            *(testData + 4*(i + j*width) + 2) = 255 * v; // green
            *(testData + 4*(i + j*width) + 3) = 255 * v; // blue
        }
    }
    testImage.save("lightnessMap.jpg");

    // Fill the mask
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            if ((*lightnessMap)(i, j) == 0.0f) {
                *(data + 4*(i + j*width) + 0) = 0; // alpha
                *(data + 4*(i + j*width) + 1) = 0; // red
                *(data + 4*(i + j*width) + 2) = 0; // green
                *(data + 4*(i + j*width) + 3) = 0; // blue
            }
            else {
                *(data + 4*(i + j*width) + 0) = 255; // alpha
                *(data + 4*(i + j*width) + 1) = 0;   // red
                *(data + 4*(i + j*width) + 2) = 0;   // green
                *(data + 4*(i + j*width) + 3) = 255; // blue
            }
        }
    }

    delete lightnessMap;
    delete R1;
    delete G1;
    delete B1;
    delete R2;
    delete G2;
    delete B2;

    return newMask;
}

QImage *HdrCreationManager::calculateAgMaskAlgo2(QRect rect, int index1, int index2, float threshold)
{
    int width = rect.width();
    int height = rect.height();
    pfs::Array2D *R1, *G1, *B1, *R2, *G2, *B2;
    
    R1 = new pfs::Array2D(width, height);
    G1 = new pfs::Array2D(width, height);
    B1 = new pfs::Array2D(width, height);
    R2 = new pfs::Array2D(width, height);
    G2 = new pfs::Array2D(width, height);
    B2 = new pfs::Array2D(width, height);

    int x_ul, y_ul, x_br, y_br;

    rect.getCoords(&x_ul, &y_ul, &x_br, &y_br);

    pfs::copyArray(listmdrR[index1], R1, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrG[index1], G1, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrB[index1], B1, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrR[index2], R2, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrG[index2], G2, x_ul, y_ul, x_br, y_br);
    pfs::copyArray(listmdrB[index2], B2, x_ul, y_ul, x_br, y_br);

    QImage *newMask = new QImage(width, height, QImage::Format_ARGB32);
    uchar *data = newMask->bits();

    qreal avgLight1 = averageLightness(R1, G1, B1);
    qreal avgLight2 = averageLightness(R2, G2, B2);
    qreal sf = avgLight1 / avgLight2;

    if (sf > 1.0f) sf = 1.0f / sf; 

    normalize(R1, G1, B1);
    normalize(R2, G2, B2);   

    float h, s, l;
    // convert to hsl (R, G and B will contain the H, S and L values)
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*R1)(i, j), (*G1)(i, j), (*B1)(i, j), &h, &s, &l); 
            (*R1)(i, j) = h;      
            (*G1)(i, j) = s;      
            (*B1)(i, j) = l;      
        }
    }    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            rgb2hsl((*R2)(i, j), (*G2)(i, j), (*B2)(i, j), &h, &s, &l); 
            (*R2)(i, j) = h;      
            (*G2)(i, j) = s;      
            (*B2)(i, j) = sf * l;      
        }
    }    
    float r, g, b;
    // back to rgb
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            hsl2rgb((*R1)(i, j), (*G1)(i, j), (*B1)(i, j), &r, &g, &b); 
            (*R1)(i, j) = r;      
            (*G1)(i, j) = g;      
            (*B1)(i, j) = b;      
        }
    }    
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            hsl2rgb((*R2)(i, j), (*G2)(i, j), (*B2)(i, j), &r, &g, &b); 
            (*R2)(i, j) = r;      
            (*G2)(i, j) = g;      
            (*B2)(i, j) = b;      
        }
    }    
    pfs::Array2D *mapR = new pfs::Array2D(width, height);
    pfs::Array2D *mapG = new pfs::Array2D(width, height);
    pfs::Array2D *mapB = new pfs::Array2D(width, height);

    computeColorDifference(R1, G1, B1, R2, G2, B2, mapR, mapG, mapB, threshold);

    histogramSegmentation(mapR, mapG, mapB, 1e-5);   

    // Fill the mask
    for (int j = 0; j < height; j++) {
        for (int i = 0; i < width; i++) {
            if ((*mapR)(i, j) == 0.0f && (*mapG)(i, j) == 0.0f && (*mapB)(i, j) == 0.0f ) {
                *(data + 4*(i + j*width) + 0) = 0; // alpha
                *(data + 4*(i + j*width) + 1) = 0; // red
                *(data + 4*(i + j*width) + 2) = 0; // green
                *(data + 4*(i + j*width) + 3) = 0; // blue
            }
            else {
                *(data + 4*(i + j*width) + 0) = 255; // alpha
                *(data + 4*(i + j*width) + 1) = 0;   // red
                *(data + 4*(i + j*width) + 2) = 0;   // green
                *(data + 4*(i + j*width) + 3) = 255; // blue
            }
        }
    }

    delete mapR;
    delete mapG;
    delete mapB;
    delete R1;
    delete G1;
    delete B1;
    delete R2;
    delete G2;
    delete B2;

    return newMask;
}

void HdrCreationManager::doAntiGhosting()
{
    int size = listmdrR.size(); 
    float HE[size];
    int width = listmdrR.at(0)->getCols();
    int height = listmdrR.at(0)->getRows();
    int midX = width >> 1;
    int midY = height >> 1;
    float k = 1.0f;

    qDebug() << "midX: " << midX;
    qDebug() << "midY: " << midY;
    
    gsl_vector *kc = gsl_vector_alloc(6);
    gsl_vector *temp_c = gsl_vector_alloc(6);
    gsl_matrix *M = gsl_matrix_alloc(6, 6);
    gsl_matrix *invertedM = gsl_matrix_alloc(6, 6);
    gsl_matrix *tempM = gsl_matrix_alloc(6, 6);
    gsl_matrix *M1 = gsl_matrix_alloc(6, 1);
    gsl_matrix *M2 = gsl_matrix_alloc(1, 6);
    gsl_matrix *m = gsl_matrix_alloc(6, 1);
    gsl_permutation* perm = gsl_permutation_alloc(6);

    gsl_vector_set_zero(kc);
    gsl_matrix_set_zero(M1);
    gsl_matrix_set_zero(M2);


    for (int i = 0; i < size; i++) 
        normalize(listmdrR.at(i), listmdrG.at(i), listmdrB.at(i));

    for (int i = 0; i < size; i++)
        transformFromRgbToHsl(listmdrR.at(i), listmdrG.at(i), listmdrB.at(i));

    for (int i = 0; i < size; i++) { 
        HE[i] = hueSquaredMean(listmdrR, i);
        qDebug() << "HE[" << i << "]: " << HE[i];
    }

    int h0 = findIndex(HE, size);

    qDebug() << "h0: " << h0;

    for (int h = 0; h < size; h++) {
        if (h == h0) continue;
        for (int j = midY - 25; j < midY + 25; j++) {
            for (int i = midX - 25; i < midX + 25; i++) {  
                k = computeK(listmdrB.at(h0), listmdrB.at(h), h0, h, i, j);
                computeC(listmdrB.at(h0), i, j, temp_c); 
                gsl_blas_dscal(k, temp_c);
                gsl_vector_add(kc, temp_c);
            }   
        }
        for (int j = midY - 25; j < midY + 25; j++) {
            for (int i = midX - 25; i < midX + 25; i++) {  
                computeC(listmdrB.at(h0), i, j, temp_c); 
                fillMatrixM1(M1, temp_c); 
                fillMatrixM2(M2, temp_c);
                cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, 6, 6, 1, 1.0f, 
                            gsl_matrix_ptr(M1, 0, 0), 1, gsl_matrix_ptr(M2, 0, 0), 6,
                            0.0f, gsl_matrix_ptr(tempM, 0, 0), 6);
                gsl_matrix_add(M, tempM);
                
            }
        }
        //printMatrix(M, 6, 6);
        int s;
        try {
            gsl_linalg_LU_decomp(M, perm, &s);
            gsl_linalg_LU_invert(M, perm, invertedM);
        }
        catch (...) {
            qDebug() << "M-1";
            break;
        }
        cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, 6, 1, 6, 1.0f, 
                    gsl_matrix_ptr(invertedM, 0, 0), 6, gsl_vector_ptr(kc, 0), 1,
                    0.0f, gsl_matrix_ptr(m, 0 ,0), 1);
        printMatrix(m, 6, 1); 
    }
    for (int i = 0; i < size; i++)
        transformFromHslToRgb(listmdrR.at(i), listmdrG.at(i), listmdrB.at(i));

    gsl_vector_free(temp_c);
    gsl_vector_free(kc);
    gsl_matrix_free(M1);
    gsl_matrix_free(M2);
    gsl_matrix_free(M);
    gsl_matrix_free(invertedM);
    gsl_matrix_free(m);
}
