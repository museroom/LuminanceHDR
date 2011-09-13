/**
 * This file is a part of Luminance HDR package.
 * ----------------------------------------------------------------------
 * Copyright (C) 2011 Davide Anastasia
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
 * Original Work
 * @author Davide Anastasia <davideanastasia@users.sourceforge.net>
 *
 */

#ifndef IGRAPHICSVIEW_H
#define IGRAPHICSVIEW_H

#include <QGraphicsScene>
#include <QGraphicsView>
#include <QWheelEvent>
#include <QResizeEvent>

class IGraphicsView : public QGraphicsView {
    Q_OBJECT
private:
    void init();

public:
    IGraphicsView ( QWidget * parent = 0 );
    IGraphicsView ( QGraphicsScene * scene, QWidget * parent = 0 );
    ~IGraphicsView();
protected:
    virtual void wheelEvent(QWheelEvent *event);
    virtual void resizeEvent(QResizeEvent* event);

Q_SIGNALS:
    void zoomIn();
    void zoomOut();
    void viewAreaChangedSize();
};

#endif
