/**
 * This file is a part of LuminanceHDR package.
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

#include "BatchTMJob.h"
#include "Fileformat/pfstiff.h"
#include "Exif/ExifOperations.h"

#include <QFileInfo>
#include <QByteArray>
#include <QDebug>

BatchTMJob::BatchTMJob(int thread_id, QString filename, const QList<TonemappingOptions*>* tm_options, QString output_folder):
        m_thread_id(thread_id),
        m_file_name(filename),
        m_tm_options(tm_options),
        m_output_folder(output_folder)
{
    m_working_frame = NULL;
    m_ldr_image     = NULL;

    m_ldr_output_format = LuminanceOptions::getInstance()->batch_ldr_format;

    m_output_file_name_base  = m_output_folder + "/" + QFileInfo(m_file_name).completeBaseName();
}

BatchTMJob::~BatchTMJob()
{

}

void BatchTMJob::run()
{
    emit add_log_message(tr("[T%1] Start processing %2").arg(m_thread_id).arg(QFileInfo(m_file_name).completeBaseName()));

    // load frame
    LoadHdrThread * load_thread = new LoadHdrThread(m_file_name);
    connect(load_thread, SIGNAL(finished()),
            load_thread, SLOT(deleteLater()));
    // in case it fails!
    // there must be a direct connection, otherwise the wait() returns BEFORE the execution of the SLOT!
    connect(load_thread, SIGNAL(load_failed(QString)),
            this, SLOT(load_hdr_failed(QString)), Qt::DirectConnection);
    // in case it passes
    // there must be a direct connection, otherwise the wait() returns BEFORE the execution of the SLOT!
    connect(load_thread, SIGNAL(hdr_ready(pfs::Frame*, QString)),
            this, SLOT(load_hdr_completed(pfs::Frame*, QString)), Qt::DirectConnection);

    load_thread->start();
    load_thread->wait();

    if ( m_working_frame != NULL )
    {
        // update message box
        emit add_log_message(tr("[T%1] Successfully load %2").arg(m_thread_id).arg(QFileInfo(m_file_name).completeBaseName()));

        // update progress bar!
        emit increment_progress_bar(1);

        TonemappingOptions* opts;
        for (int idx = 0; idx < m_tm_options->size(); idx++)
        {
            opts = m_tm_options->at(idx);

            opts->tonemapSelection = false; // just to be sure!
            opts->origxsize = m_working_frame->getWidth();
            //opts->xsize = 400; // DEBUG
            //opts->xsize = opts->origxsize;

            TMOThread * tmo_thread = TMOFactory::getTMOThread(opts->tmoperator, m_working_frame, opts);

            // Thread deletes itself when it has done with its job
            connect(tmo_thread, SIGNAL(finished()),
                    tmo_thread, SLOT(deleteLater()));
            // there must be a direct connection, otherwise the wait() returns BEFORE the execution of the SLOT!
            connect(tmo_thread, SIGNAL(imageComputed(QImage*, quint16*, const TonemappingOptions*)),
                    this, SLOT(tm_completed(QImage*, quint16*, const TonemappingOptions*)), Qt::DirectConnection);

            //start thread
            tmo_thread->set_batch_mode();
            tmo_thread->start();
            tmo_thread->wait();

            if ( m_ldr_image != NULL && m_pixmap != NULL)
            {
                // ldr and pixmap are available
                TMOptionsOperations operations(opts);

                QString output_file_name = m_output_file_name_base+"_"+operations.getPostfix()+"."+m_ldr_output_format;
				QFileInfo qfi(output_file_name);
    			QString absoluteFileName = qfi.absoluteFilePath();
			    QByteArray encodedName = QFile::encodeName(absoluteFileName);
				
				if (m_ldr_output_format == "TIFF")
				{

					int width = m_ldr_image->width();
					int height = m_ldr_image->height();
					try
					{
			        	TiffWriter tiffwriter(encodedName, m_pixmap, width, height);
						tiffwriter.write16bitTiff();
                    	emit add_log_message( tr("[T%1] Successfully saved LDR file: %2").arg(m_thread_id).arg(QFileInfo(output_file_name).completeBaseName()) );
					}
					catch(...)
					{
                    	emit add_log_message( tr("[T%1] ERROR: Cannot save to file: %2").arg(m_thread_id).arg(QFileInfo(output_file_name).completeBaseName()) );
					}
				}
				else
				{
                	qDebug() << "Batch saved quality: " << opts->quality;
                	if (!m_ldr_image->save(output_file_name, m_ldr_output_format.toLocal8Bit(), opts->quality))
                	{
                    	emit add_log_message( tr("[T%1] ERROR: Cannot save to file: %2").arg(m_thread_id).arg(QFileInfo(output_file_name).completeBaseName()) );
                	}
                	else
                	{
                    	// ExifOperations methods want a std::string, we need to use the QFile::encodeName(QString)[.constData()] (constData() is implicit if you omit it)
                    	// trick to cope with local 8-bit encoding determined by the user's locale.
                    	ExifOperations::writeExifData(QFile::encodeName(output_file_name).constData(), operations.getExifComment().toStdString());

                    	emit add_log_message( tr("[T%1] Successfully saved LDR file: %2").arg(m_thread_id).arg(QFileInfo(output_file_name).completeBaseName()) );
                	}

                // reset for the next TM
                	delete m_ldr_image;
                	m_ldr_image = NULL;
            	}
			}
            // update progress bar
            emit increment_progress_bar(1);
        }
        delete m_working_frame;
    }
    else
    {
        // update message box
        //emit add_log_message(error_message);
        emit add_log_message(tr("[T%1] ERROR: Loading of %2 failed").arg(m_thread_id).arg(QFileInfo(m_file_name).completeBaseName()));

        // update progress bar!
        emit increment_progress_bar(m_tm_options->size() + 1);
    }

    emit done(m_thread_id);
}

void BatchTMJob::load_hdr_failed(QString /*error_message*/)
{
    // better be sure that run() finds a null pointer
    m_working_frame = NULL;
}

void BatchTMJob::load_hdr_completed(pfs::Frame* hdr_loaded, QString /*filename*/)
{
    m_working_frame = hdr_loaded;
}

void BatchTMJob::tm_failed()
{
    m_ldr_image = NULL;
}

void BatchTMJob::tm_completed(QImage* newimage, quint16* newpixmap, const TonemappingOptions* /*opts*/)
{
    m_ldr_image = newimage;
	m_pixmap = newpixmap;
}
